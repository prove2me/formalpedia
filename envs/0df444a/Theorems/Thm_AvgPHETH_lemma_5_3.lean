-- Prove2me | Theorems.Thm_AvgPHETH_lemma_5_3
-- name    : AvgPHETH.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:36:25.692486+00:00
-- url     : https://prove2.me/theorems/c5c1a031-6514-4c83-ac4e-42122e295b1f
-- title:
--   Lemma 5.3 — telescoped amortized bound $(m+O(\log t_I))/I+2|z|/R$
-- statement:
--   In the setting of Lemma 5.2, there are a constant $c\ge2$ and a time requirement $p$ for which the conclusion of Lemma 5.2 holds and such that the following holds. Let $t_0$ satisfy this time requirement and set $t_{j+1}=t_j^c$. For every integer $I\ge1$,
--
--   $$\frac1R\sum_{i=1}^R K^{t_I,O}(a_i\mid\tau_{<i},q_i)\le\frac{m+O(\log t_I)}{I}+\frac{2|z|}{R}.$$
--
--   The depth telescopes over $I$ time scales, which turns the bound of Lemma 5.2 into an amortized saving of a factor $I$ in the description length.
--
--   Differences from the source:
--   - generalization: the unrelativized statement under $\mathrm{Dist}\Sigma_{d+1}^p\subseteq\mathrm{AvgP}$ → relative to every oracle $O$, under $\Sigma_{d+1}^{p,O}\times\{\mathcal U,\mathcal T\}\subseteq\mathrm{AvgP}^O$; reason: Remark 6.4 (p.28) and p.30 relativize it and weaken the hypothesis; at $O=\emptyset$ the footnote on p.10 gives the hypothesis from the printed one
--   - generalization: an efficient universal machine $U$, fixed once → every $U$ with polynomial overhead (IsEfficientUniversal); reason: the page prints no overhead bound; the usual efficient machines have polynomial overhead, so this specializes to any of them
--   - encoding: oracle access to $A$ → oracle $O\oplus A$; reason: at $O=\emptyset$ the tag on each query is the only change, with polynomial overhead
--   - reading: "the constant $c$ from that lemma" and "its time requirement" → constants $c\ge2$, $e$, $C$ for which the conclusion of Lemma 5.2 holds (restated as the first conjunct), then the bound for $t_0\ge(n+|z|+R+m+\mathrm{time}_f+2)^e+e$ and $t_I=t_0^{c^I}$; reason: Lemma 5.2 asserts its $c$ and $p$ only to exist and they are not unique; the statement ties Lemma 5.3 to one such choice, as the proof on pp.21–22 does
--   - reading: "for every $z$" → $|z|\le r(n)$, with $r$ a polynomial; reason: the section preamble defines $f_n$ on $z\in\{0,1\}^{\le\mathrm{poly}(n)}$ only
--   - encoding: the condition $(\tau_{<i},q_i)$ and the tuple $\boldsymbol q$ → binTuple of the flat tuple $(q_1,a_1,\dots,q_{i-1},a_{i-1},q_i)$ and of $(q_1,\dots,q_R)$; reason: the page fixes some encoding of tuples (p.18), and the flat transcript is generated in polynomial time from $\langle\tau_{<i},q_i\rangle$ (p.21)
--   - encoding: sums of $K^t$ values and $\log t$ → sums in $\mathbb R_{\ge0}\cup\{\infty\}$ with $K^t=\infty$ when no program exists; base-2 logarithm; reason: Lean convention; a finite value is unchanged
-- source:
--   Hirahara–Juvekar–Nanashima, Average-Case Hardness of PH from ETH-Type Hypotheses, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), Lemma 5.3, p.21 (PDF 23)

import Mathlib
import Definitions.Def_AvgPHETH_IsEfficientUniversal
import Definitions.Def_AvgPHETH_TimesUT
import Definitions.Def_AvgPHETH_SigmaPO
import Definitions.Def_AvgPHETH_Kt
import Definitions.Def_AvgPHETH_oJoin
import Definitions.Def_AvgPHETH_IsRespFamily
import Definitions.Def_AvgPHETH_transcript
import Definitions.Def_AvgPHETH_binTuple
open KarpLiptonOM
open scoped ENNReal

namespace AvgPHETH

/-- **Lemma 5.3** (Hirahara–Juvekar–Nanashima, *Average-Case Hardness of PH from ETH-Type Hypotheses*, manuscript of November 3, 2026 (STOC 2027 submission; held version sha256 ea5fd472…), p.21 (PDF 23)), in the setting of Lemma 5.2, relative to every oracle `O`. Let `t₀` satisfy the time
requirement of Lemma 5.2 and set `t_{j+1} = t_j^c`. For every integer `I ≥ 1`,
`(1/R) ∑_i K^{t_I}(a_i | τ_{<i}, q_i) ≤ (m + O(log t_I))/I + 2|z|/R`.

**Formalization Note** `t_I = t₀^(c^I)`. "The constant `c` from that lemma" and "its time requirement" are tied to
Lemma 5.2: the statement asserts constants `c ≥ 2`, `e`, `C` for which the conclusion of Lemma 5.2 holds (restated as the first
conjunct, with time requirement `(…)^e + e`), and, for these `c` and `e`, the telescoped bound. The constant of `O(log t_I)` is the
named `C'`, which does not depend on `R, n, z, q, I, t₀`. -/
theorem lemma_5_3 (U : OracleTM) (hU : IsEfficientUniversal U) (O : Set (List Bool)) (d : ℕ)
    (hd : 1 ≤ d) (hAvg : TimesUT O (SigmaPO O (d + 1))) (A : Set (List Bool))
    (hA : A ∈ SigmaPO O d) (m ℓ : ℕ → ℕ) (timef : ℕ → ℕ → ℕ) (r : Polynomial ℕ) (M : OracleTM)
    (hm : ∀ n, 1 ≤ m n) (hℓ : ∀ n, 1 ≤ ℓ n) (hf : IsRespFamily M (oJoin O A) timef m ℓ r) :
    ∃ c e C : ℕ, 2 ≤ c ∧
      (∀ (n : ℕ) (z : List Bool), z.length ≤ r.eval n →
        ∀ (R : ℕ), 1 ≤ R → ∀ q : Fin R → List Bool, (∀ i, (q i).length = m n) →
        ∀ t : ℕ, (n + z.length + R + m n + timef n z.length + 2) ^ e + e ≤ t →
          ∑ i : Fin R, ((Kt U O (t ^ c) (resp M (oJoin O A) timef n z (q i))
                (transcript (resp M (oJoin O A) timef n z) q i) : ℕ∞) : ℝ≥0∞) +
              ((Kt U O (t ^ c) (binTuple (List.ofFn q)) [] : ℕ∞) : ℝ≥0∞) ≤
            ((Kt U O t (binTuple (List.ofFn q)) [] : ℕ∞) : ℝ≥0∞) + 2 * (z.length : ℝ≥0∞) +
              ENNReal.ofReal ((R : ℝ) * (C : ℝ) * Real.logb 2 t)) ∧
      ∃ C' : ℕ, ∀ (n : ℕ) (z : List Bool), z.length ≤ r.eval n →
        ∀ (R : ℕ), 1 ≤ R → ∀ q : Fin R → List Bool, (∀ i, (q i).length = m n) →
        ∀ t₀ : ℕ, (n + z.length + R + m n + timef n z.length + 2) ^ e + e ≤ t₀ →
        ∀ I : ℕ, 1 ≤ I →
          (R : ℝ≥0∞)⁻¹ * ∑ i : Fin R, ((Kt U O (t₀ ^ (c ^ I)) (resp M (oJoin O A) timef n z (q i))
                (transcript (resp M (oJoin O A) timef n z) q i) : ℕ∞) : ℝ≥0∞) ≤
            ENNReal.ofReal
              (((m n : ℝ) + (C' : ℝ) * Real.logb 2 ((t₀ ^ (c ^ I) : ℕ) : ℝ)) / (I : ℝ) +
                2 * (z.length : ℝ) / (R : ℝ)) := by sorry

end AvgPHETH
