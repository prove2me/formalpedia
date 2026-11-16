-- Prove2me | Theorems.Thm_AcceptSubcube_Supplement_theorem_1_2
-- name    : AcceptSubcube.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:50:31.460723+00:00
-- url     : https://prove2.me/theorems/7ff2aacc-b5cb-4107-bc3f-89e65ebbd57e
-- title:
--   Theorem 1.2 — hardness of complete signed thresholds: no constant factor at $h=2$ (UGC), no $O(n^{h-2-\varepsilon})$ at $h\ge3$
-- statement:
--   The following hold for complete unweighted instances with positive optimum ($\mathrm{OPT}\ge1$).
--
--   **(a) Accepting-subcube dimension 2.** Assume the Unique Games Conjecture. For every $k\ge3$, every constant $\rho$ and every $p_0>0$: if a randomized polynomial-time algorithm outputs, on every complete signed $\mathrm{THR}_{k,k-2}$ instance with $\mathrm{OPT}\ge1$, an assignment $Y$ with $\Pr[C_{\mathcal I}(Y)\le\rho\,\mathrm{OPT}]\ge p_0$, or with $\mathbb E[C_{\mathcal I}(Y)]\le\rho\,\mathrm{OPT}$, then $\mathsf{NP}\subseteq\mathsf{BPP}$. If a deterministic polynomial-time algorithm achieves $C_{\mathcal I}(Y)\le\rho\,\mathrm{OPT}$ on these instances, then $\mathsf P=\mathsf{NP}$.
--
--   **(b) Accepting-subcube dimension at least 3.** Fix $3\le h\le k-1$, $0<\varepsilon<h-2$ and $c>0$. Let $\mathcal D$ be the complete signed $\mathrm{THR}_{k,k-h}$ instances with $\mathrm{OPT}\ge1$, and, when $h=k-1$ (complete Min-$k$-SAT), also $C_{\mathcal I}(\mathbf 1)\le n^{k-3}$, where $\mathbf 1$ is the all-one assignment. If a randomized polynomial-time algorithm achieves on $\mathcal D$
--   $$\Pr\big[C_{\mathcal I}(Y)\le c\,n^{h-2-\varepsilon}\,\mathrm{OPT}\big]\ge p_0\quad\text{for some }p_0>0,\qquad\text{or}\qquad\mathbb E[C_{\mathcal I}(Y)]\le c\,n^{h-2-\varepsilon}\,\mathrm{OPT},$$
--   then $\mathsf{NP}=\mathsf{RP}$; a deterministic polynomial-time algorithm with this ratio on $\mathcal D$ gives $\mathsf P=\mathsf{NP}$.
--
--   Together with Theorem 1.1 this pins down the polynomial exponent $h-2$ of the class $\mathcal C_{k,h}$, and shows that the constant factor at $h=1$ cannot be extended to $h=2$ under the UGC.
--
--   **Formalization Note** $\mathsf{NP}$, $\mathsf{RP}$, $\mathsf{BPP}$, $\mathsf P$ are classes of the published `CookPvsNP` model over every finite alphabet; the UGC is the published `OptInapprox.MaxCut.UGC`. Algorithms are TM2 machines as in Theorem 1.1. The algorithm is assumed only on the instances the theorem names.
--
--   Differences from the source:
--   - reading: a randomized (resp. deterministic) polynomial-time algorithm → a TM2 polynomial-time machine (Turing.TM2ComputableInPolyTime) on (instance, coin string) with coin strings of length p(|enc I|) for a polynomial p fixed before the instance, probabilities and expectations taken over the exact uniform distribution on those coin strings (resp. a TM2 polynomial-time machine on the instance alone); reason: the paper names no machine model; fair coins are its model (p.28); this is the convention of the published theorem_1_1
--   - encoding: NP, RP, BPP, P and the UGC → the classes of the published CookPvsNP model over every finite alphabet (RP and BPP as polynomial-time checking relations on (input, coin string) with coin strings of length |w|^k + k), and the published OptInapprox.MaxCut.UGC; reason: one machine model for every class in a statement, the model of the published UGC; these are the standard classes
--   - reading: Assume the UGC and NP ⊄ BPP … admits no randomized polynomial-time constant-factor approximation → UGC → (a randomized ρ-approximation succeeding with probability ≥ p₀ > 0, or in expectation, on the instances → NP ⊆ BPP), for every real ρ; reason: contrapositive; 'randomized approximation' is read with the weakest success notions the proof covers (§8.4: probability p₀ or expectation, as in (b)), which gives the strongest statement
--   - reading: for complete unweighted instances with positive optimum; for h = k − 1 the hard instances satisfy 1 ≤ OPT ≤ C_I(1) ≤ n^{k−3} → the algorithm is assumed only on complete signed instances with OPT ≥ 1, and for h = k − 1 also with C_I(1) ≤ n^{k−3} (OPT ≤ C_I(1) always holds); reason: the theorem's opening sentence and its last sentence of (b) restrict the instances on which the algorithm must work; this is the strong form of the statement
--   - encoding: O(n^{h−2−ε})-approximation → c·n^{h−2−ε}·OPT on every instance of the family, for every constant c > 0; reason: finitely many instances exist for each n and n^{h−2−ε} ≥ 1 for n ≥ 1, so a threshold n₀ is absorbed into c
-- source:
--   Cai, Jiang, Liu, Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs, STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.2, pp.4–5 (proofs: §7.2–7.3, Lemmas 7.2, 7.3, pp.35–37; §8, Lemmas 8.1–8.3, §8.4, pp.43–46)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_AcceptSubcube_GInst
import Definitions.Def_AcceptSubcube_cost
import Definitions.Def_AcceptSubcube_Supplement_RP
import Definitions.Def_AcceptSubcube_Supplement_CompleteSigned
import Definitions.Def_AcceptSubcube_Supplement_RandApproxOn

namespace AcceptSubcube.Supplement

open AcceptSubcube

/-- **Theorem 1.2 (Hardness).**

Cai, Jiang, Liu, *Accepting Subcubes and the Approximability of Complete Boolean Min-CSPs*,
STOC 2027 submission (manuscript sha256 66626baf…), Theorem 1.2, pp.4–5: "The following hold for
complete unweighted instances with positive optimum, produced by deterministic reductions.
(a) Assume the UGC and NP ⊄ BPP. For every fixed k ≥ 3, complete signed THR_{k,k−2} admits no
randomized polynomial-time constant-factor approximation. (b) Fix 3 ≤ h ≤ k − 1 and
0 < ε < h − 2. A randomized polynomial-time O(n^{h−2−ε})-approximation for complete signed
THR_{k,k−h}, succeeding with a fixed positive probability or in expectation, implies NP = RP. For
h = k − 1 this is complete Min-k-SAT, and the hard instances satisfy 1 ≤ OPT ≤ C_I(1) ≤ n^{k−3},
where 1 is the all-one assignment. For deterministic algorithms the conclusions are P = NP, under
the UGC in (a)."

Under the UGC, for every `k ≥ 3`, every constant `ρ` and every `p₀ > 0`: a randomized
polynomial-time `ρ`-approximation on the complete signed `THR_{k,k−2}` instances with `OPT ≥ 1`,
succeeding with probability `≥ p₀` or in expectation, gives `NP ⊆ BPP`; a deterministic one gives
`P = NP`. For `3 ≤ h ≤ k − 1`, `0 < ε < h − 2`, `c > 0`, `p₀ > 0`: a randomized polynomial-time
`c·n^{h−2−ε}`-approximation on the complete signed `THR_{k,k−h}` instances with `OPT ≥ 1` (and, when
`h = k − 1`, `C_I(1) ≤ n^{k−3}`), with probability `≥ p₀` or in expectation, gives `NP = RP`; a
deterministic one gives `P = NP`.

**Formalization Note.** Algorithms are TM2 machines (`RandApproxOn`, `RandApproxExpOn`,
`DetApproxOn`); `NP`, `RP`, `BPP`, `P` are classes of the published `CookPvsNP` model, the model
of the published `UGC`. "Constant factor" is a real constant `ρ` (every `ρ`); `O(n^{h−2−ε})` is
`c·n^{h−2−ε}` on every instance of the family (equivalent here: each `n` has finitely many instances,
and `n^{h−2−ε} ≥ 1` for `n ≥ 1`). The algorithm is assumed only on the instances the theorem names
(positive optimum; for `h = k − 1` also `C_I(1) ≤ n^{k−3}`, and `OPT ≤ C_I(1)` always holds), which
makes the statement stronger than one about all complete instances. -/
theorem theorem_1_2 :
    (OptInapprox.MaxCut.UGC → ∀ k : ℕ, 3 ≤ k →
      (∀ ρ p₀ : ℝ, 0 < p₀ →
        RandApproxOn (fun I => CompleteSigned (thr (k - 2)) k I ∧ 1 ≤ OPT I) (fun _ => ρ) p₀ →
          NPsubBPP) ∧
      (∀ ρ : ℝ,
        RandApproxExpOn (fun I => CompleteSigned (thr (k - 2)) k I ∧ 1 ≤ OPT I) (fun _ => ρ) →
          NPsubBPP) ∧
      (∀ ρ : ℝ,
        DetApproxOn (fun I => CompleteSigned (thr (k - 2)) k I ∧ 1 ≤ OPT I) (fun _ => ρ) →
          PeqNP)) ∧
    (∀ k h : ℕ, 3 ≤ h → h ≤ k - 1 → ∀ ε c : ℝ, 0 < ε → ε < (h : ℝ) - 2 → 0 < c →
      let D : GInst → Prop := fun I => CompleteSigned (thr (k - h)) k I ∧ 1 ≤ OPT I ∧
        (h = k - 1 → cost I (fun _ => true) ≤ I.n ^ (k - 3))
      let ρ : GInst → ℝ := fun I => c * (I.n : ℝ) ^ ((h : ℝ) - 2 - ε)
      (∀ p₀ : ℝ, 0 < p₀ → RandApproxOn D ρ p₀ → NPeqRP) ∧
      (RandApproxExpOn D ρ → NPeqRP) ∧
      (DetApproxOn D ρ → PeqNP)) := by sorry

end AcceptSubcube.Supplement
