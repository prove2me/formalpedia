-- Prove2me | Theorems.Thm_DNFSatMQ_Main_lemma_4_5
-- name    : DNFSatMQ.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:34:31.314017+00:00
-- url     : https://prove2.me/theorems/f27351d4-78e7-4fa4-8c99-ba71c79cf1ba
-- title:
--   Lemma 4.5 — Algorithm 2 outputs exactly (1−r)U_H + rδ_⊥ with r ≤ ε/2, and both TV bounds
-- statement:
--   Let $F\subseteq\{0,1\}^n$ be nonempty (the satisfying set of the target), $\varepsilon\in(0,1)$, $\gamma\in(0,1]$, $c_1,\dots,c_m$ conjunctions and $h_1,\dots,h_m$ local hypotheses, and assume the calls of Algorithm 1 satisfy their guarantees: $|F\setminus G|\le(\varepsilon/4)|F|$ for $G=\bigcup_iC_i$, $\sum_i|C_i|\le|F|/\gamma$, and $\Pr_{x\sim U_{C_i}}[h_i(x)\ne f(x)]\le\varepsilon_0 = \varepsilon\gamma/4$ for every $i$. Let $h$ be the hypothesis (3), $H = h^{-1}(1)$, $W=\sum_i|C_i|$ and $t = \lceil(2/\gamma)\log(2/\varepsilon)\rceil$. Then $H\neq\emptyset$ and Algorithm 2 outputs the law
--   $$D_h = (1-r)\,U_H + r\,\delta_\bot,\qquad r = \Big(1-\frac{|H|}{W}\Big)^t\le\frac\varepsilon2, \tag{5}$$
--   and moreover $d_{TV}(U_H,U_F)\le\varepsilon/2$, $d_{TV}(D_h,U_H) = r\le\varepsilon/2$, hence $d_{TV}(D_h,U_F)\le\varepsilon$. All laws live on $\{0,1\}^n\cup\{\bot\}$ with $U_H(\bot)=U_F(\bot)=0$; the mixture is stated pointwise.
--
--   Differences from the source:
--   - encoding: a term: literals on distinct variables → a partial assignment `Conj n = Fin n → Option Bool`; reason: §2 defines terms as noncontradictory; same objects
--   - encoding: coordinates [n] = {1, …, n} and bits {0, 1} → `Fin n` (coordinates 0, …, n−1) and `Bool`; reason: Lean convention; same instances
--   - reading: log in t = ⌈(2/γ) log(2/ε)⌉ → natural logarithm (`Real.log`); reason: §4 does not fix the base; the proof uses r ≤ e^{−p_a t}, which needs t ≥ (2/γ) ln(2/ε); base 2 would give a larger t
--   - generalization: hᵢ returned by A_learn, a function of the free coordinates of cᵢ → hᵢ any function {0,1}ⁿ → {0,1} with the stated error on U_{Cᵢ}; reason: the lemma uses only the error bound; the paper itself regards hᵢ as a function on {0,1}ⁿ
--   - encoding: f a nonempty s-term DNF with F = f⁻¹(1) → F any nonempty set of points, f(x) = [x ∈ F]; reason: every Boolean function is a DNF; s does not enter the lemma
--   - encoding: the weighted choice of cᵢ followed by x ∼ U_{Cᵢ} → a uniform draw from the pairs {(i, x) : x ∈ Cᵢ}; reason: the same joint law (probability |Cᵢ|/W for i, then uniform x)
-- source:
--   Zelin Li, Learning DNF from Satisfying Assignments with Membership Queries, STOC 2027 submission (manuscript sha256 2e246dc4…2670), Lemma 4.5, p. 12 (PDF 13)

import Mathlib
import Definitions.Def_DNFSatMQ_Main_Reduction
import Definitions.Def_DNFSatMQ_Main_Machine

namespace DNFSatMQ.Main

/-- Lemma 4.5 (p. 12). The guarantees of the calls in Algorithm 1 are the densifier's at accuracy
`ε/4` with volume parameter `γ`, and the local learners' at accuracy `ε₀ = εγ/4`; `h` is (3) and
`t = ⌈(2/γ) log(2/ε)⌉`. -/
theorem lemma_4_5 {n m : ℕ} (F : Finset (Pt n)) (hF : F.Nonempty) (ε γ : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (c : Fin m → Conj n) (hs : Fin m → Pt n → Bool)
    (hcov : ((F \ Finset.univ.filter fun x => ∃ i, (c i).Sat x).card : ℝ) ≤ ε / 4 * F.card)
    (hvol : (∑ i, ((c i).cube.card : ℝ)) ≤ F.card / γ)
    (hloc : ∀ i, errOnConj (c i) (hs i) F ≤ ε * γ / 4) :
    ∃ hH : (Finset.univ.filter fun x => combinedHyp c hs x = true).Nonempty,
      (∀ o : Option (Pt n),
        (algorithm2 c hs (numTrials γ ε) o).toReal =
          (1 - (1 - ((Finset.univ.filter fun x => combinedHyp c hs x = true).card : ℝ) /
                (∑ i, ((c i).cube.card : ℝ))) ^ numTrials γ ε) *
              (unifBot (Finset.univ.filter fun x => combinedHyp c hs x = true) hH o).toReal +
            (1 - ((Finset.univ.filter fun x => combinedHyp c hs x = true).card : ℝ) /
                (∑ i, ((c i).cube.card : ℝ))) ^ numTrials γ ε * (if o = none then 1 else 0)) ∧
      (1 - ((Finset.univ.filter fun x => combinedHyp c hs x = true).card : ℝ) /
          (∑ i, ((c i).cube.card : ℝ))) ^ numTrials γ ε ≤ ε / 2 ∧
      SSNonExt.TV (unifBot (Finset.univ.filter fun x => combinedHyp c hs x = true) hH)
          (unifBot F hF) ≤ ε / 2 ∧
      SSNonExt.TV (algorithm2 c hs (numTrials γ ε))
          (unifBot (Finset.univ.filter fun x => combinedHyp c hs x = true) hH) =
        (1 - ((Finset.univ.filter fun x => combinedHyp c hs x = true).card : ℝ) /
          (∑ i, ((c i).cube.card : ℝ))) ^ numTrials γ ε ∧
      SSNonExt.TV (algorithm2 c hs (numTrials γ ε)) (unifBot F hF) ≤ ε := by sorry

end DNFSatMQ.Main
