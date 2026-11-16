-- Prove2me | Theorems.Thm_DRSub4633_Supplement_theorem_6_3
-- name    : DRSub4633.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T18:36:13.242463+00:00
-- url     : https://prove2.me/theorems/c2598a94-5710-4ebd-8bfd-1e6d0e559f42
-- title:
--   Theorem 6.3 — uniform $C^1$ offline $(\alpha_0-\varepsilon)$-approximation with polynomially many exact oracle calls
-- statement:
--   Let $Q=[0,1]^n$ and $\alpha_0=54440750000/117486474169>0.4633$. In the exact-oracle model (6), an algorithm sees a fixed objective $f$ only through exact values $f(y)$ and exact gradients $\nabla f(y)$ at points $y\in Q$. It sees the feasible set $K$ only through an ordinary linear maximization oracle (LMO), whose tie-breaking is fixed and Borel measurable, and, in the second variant, also through a Euclidean projection oracle onto the width-normalized set $K_W$ of (100). Let $\mathrm{OPT}=\max_{x\in K}f(x)$.
--
--   **Theorem 6.3.** There is an absolute constant $C>0$ with the following property. For every dimension $n$ and every $0<\varepsilon<1$:
--
--   1. **(LMO only.)** There is a randomized oracle algorithm, depending only on $n$ and $\varepsilon$, with the following property. Let $f$ be any nonnegative $C^1$ DR-submodular function on $Q$, $K\subseteq Q$ any nonempty, compact, convex, down-closed set, and the LMO any Borel measurable selection. Then every run stops with an output $y\in K$, after at most $C(n+n^6\varepsilon^{-8})$ LMO calls, at most $C(1+n^6\varepsilon^{-8})$ value and gradient queries (all at points of $Q$), and no projection calls. Moreover
--   $$\mathbb E f(y)\ge(\alpha_0-\varepsilon)\,\mathrm{OPT}.\tag{104}$$
--   2. **(Projection variant.)** With a projection oracle onto $K_W$ as well, there is an algorithm with the same guarantee, whose every run makes at most $n$ LMO calls, at most $Cn^3\varepsilon^{-4}$ projection calls and at most $C(1+n^3\varepsilon^{-4})$ value and gradient queries.
--
--   The bounds do not depend on coordinate widths, gradient magnitudes or a smoothness modulus. The approximation coefficient $\alpha_0$ is therefore achievable with polynomially many exact oracle calls over the whole class of nonnegative $C^1$ DR-submodular objectives. This is the offline consequence of the affine comparison (Theorem 4.1).
--
--   **Formalization Note** An algorithm is a `Strategy`: a probability space of seeds, chosen together with the algorithm, and a rule mapping the seed and the transcript of exact answers to the next query or to the output. Computation and sampling are free (p.8: "Counts refer to exact-real oracle calls"). Counts are worst case over seeds and over admissible oracle selections. $\mathrm{OPT}$ is written as $\sup f(K)$, which is attained. The expectation is a Bochner integral, and its integrability is part of the conclusion. $K_W$ is embedded in $\mathbb R^n$ with its deleted coordinates fixed at $0$.
--
--   Differences from the source:
--   - reading: the exact-oracle model (6); a randomized algorithm; O(·) counts of exact-real oracle calls → a Strategy: a seed from a probability space (Ω, P) chosen with the algorithm, and each next query or output an arbitrary function of the seed and the exact answers so far; only oracle calls are counted, worst case over seeds and admissible oracle selections; reason: p.8: 'Counts refer to exact-real oracle calls, with the scalar arithmetic and sampling operations of the field construction'; the proof's horizons are deterministic, so worst-case counts are what it gives
--   - reading: 'let f … and let K …. For every 0 < ε < 1 there is a randomized algorithm' in the exact-oracle model (6) → the algorithm (Ω, P, A) is chosen after n and ε and before f, K and the oracle selections (∃ algorithm ∀ f K oracles); reason: in model (6) the algorithm sees f and K only through the oracles (p.8), so one algorithm per (n, ε) serves every instance; letting it depend on f or K would make (104) trivial
--   - reading: O(·) bounds that 'do not depend on coordinate widths, gradient magnitudes, or a smoothness modulus' → one constant C > 0 chosen before n, ε, f, K and the oracle selections, with explicit bounds C(n + n⁶/ε⁸), C(1 + n⁶/ε⁸), C n³/ε⁴, C(1 + n³/ε⁴); reason: the paper's constants are absolute (c_FW, C_int and the horizons are explicit in the proof)
--   - reading: 'in addition to the n initial LMO calls' (projection variant) → the projection-variant algorithm makes at most n LMO calls; reason: the n width computations are its only LMO calls
--   - reading: an ordinary LMO with fixed Borel measurable tie-breaking → the algorithm must succeed for every map FTPLLinBandit.IsArgmaxSel K lmo (a Borel measurable maximizer selection); reason: the tie-breaking is fixed but not specified by the paper, so the guarantee is for each such selection
--   - encoding: K_W ⊆ [0,1]^{n′} after deleting zero-width coordinates; projection oracle onto K_W → K_W embedded in ℝⁿ with zero-width coordinates fixed at 0; the projection oracle answers the Euclidean projection onto the embedded set; reason: the two projections agree on the kept coordinates and the embedded one is 0 on the deleted ones; with free scalar computation each oracle gives the other
--   - encoding: exact cube value and gradient queries counted (as 'objective queries') → value and gradient queries counted together (objCount) and required at points of Q (CubeQueries); reason: a bound on the sum is the same O(·) statement; the oracles are available only on Q
--   - encoding: OPT = max_{x∈K} f(x); E f(y) → sSup (f '' K); the Bochner integral of f ∘ result, with its integrability asserted; reason: f is continuous on the compact nonempty K, so the supremum is attained; f is bounded on K ∋ y, so E f(y) is a finite expectation
--   - encoding: objective on Q, nonnegative, C1 and DR-submodular, boundary derivatives the continuous extensions → f a total function on EuclideanSpace ℝ (Fin n) with hypotheses on the cube only; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, derivatives within the cube); gradient oracle GeomDRSub.gradQ f; reason: Lean convention; values off the cube are never read
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Theorem 6.3, p.37 (model: Section 3.1, pp.7–8, Eq. (6); K_W: Eq. (100), pp.35–36)

import Mathlib
import Definitions.Def_GeomDRSub_cube
import Definitions.Def_GeomDRSub_gradQ
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_GeomDRSub_IsDownClosed
import Definitions.Def_OrabonaOL_OGD_IsEuclideanProj
import Definitions.Def_DRSub4633_alpha0
import Definitions.Def_DRSub4633_Supplement_result
import Definitions.Def_DRSub4633_Supplement_lmoCount
import Definitions.Def_DRSub4633_Supplement_projCount
import Definitions.Def_DRSub4633_Supplement_objCount
import Definitions.Def_DRSub4633_Supplement_CubeQueries
import Definitions.Def_FTPLLinBandit_IsArgmaxSel
import Definitions.Def_DRSub4633_Supplement_KW

namespace DRSub4633.Supplement

open MeasureTheory

/-- **Theorem 6.3 (Uniform C1 offline approximation).** Aggarwal–Du, *0.4633-Approximation for
Online and Offline Non-Monotone DR-Submodular Maximization*, arXiv:2610.21072, Theorem 6.3, p.37:
"In the exact-oracle model (6), let `f` be nonnegative, `C1`, and DR-submodular on the cube, and
let `K` be nonempty, compact, convex, and down-closed. For every `0 < ε < 1` there is a randomized
algorithm returning `y ∈ K` with `E f(y) ≥ (α₀ − ε) OPT`. (104) Using ordinary LMOs only, it makes
`O(n + n⁶ε⁻⁸)` LMO calls and `O(1 + n⁶ε⁻⁸)` exact cube value and gradient queries. If, in addition
to the `n` initial LMO calls, a Euclidean projection oracle over the width-normalized set `K_W` is
available, it instead uses `O(n³ε⁻⁴)` projections and `O(1 + n³ε⁻⁴)` objective queries. The bounds
do not depend on coordinate widths, gradient magnitudes, or a smoothness modulus."

There is an absolute constant `C > 0` such that for every dimension `n` and every `0 < ε < 1`:
1. (LMO only) there is a randomized oracle algorithm (a probability space `(Ω, P)` and a
   strategy `A`) such that, for every nonnegative `C¹` DR-submodular `f` on `Q`, every nonempty
   compact convex down-closed `K ⊆ Q`, and all oracles answering exact values `f`, exact
   gradients `∇f` (within the cube), and LMO replies by any Borel measurable maximizer selection,
   every run stops with an output `y ∈ K` after at most `C(n + n⁶ε⁻⁸)` LMO calls, at most
   `C(1 + n⁶ε⁻⁸)` value/gradient queries, all at points of `Q`, and no projection calls; and
   `E f(y) ≥ (α₀ − ε) OPT` with `OPT = max_{x∈K} f(x)`;
2. (projection variant) the same with the projection oracle onto `K_W` answering exactly: every
   run makes at most `n` LMO calls, at most `C n³ε⁻⁴` projection calls and at most
   `C(1 + n³ε⁻⁴)` value/gradient queries.

**Formalization Note.** The exact-oracle model (6) is the real-RAM oracle model of `Strategy`:
only oracle calls are counted (p.8, "Counts refer to exact-real oracle calls"), and the algorithm
depends only on `n` and `ε` (it is chosen before `f`, `K` and the oracle selections). Counts are
worst case over seeds and admissible oracle selections. The LMO is any Borel measurable
maximizer selection, the published `FTPLLinBandit.IsArgmaxSel` (p.7: "tie-breaking is fixed and
Borel measurable"). `OPT` is `sSup (f '' K)`, attained for
`f` continuous on the compact `K`. The expectation is the Bochner integral, with integrability
asserted. `K_W` is embedded in `ℝⁿ` (see `KW`). `α₀` is the base mission's `DRSub4633.alpha0`. -/
theorem theorem_6_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (A : Strategy n Ω),
        IsProbabilityMeasure P ∧
        ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (K : Set (EuclideanSpace ℝ (Fin n)))
          (O : Oracles n),
          (∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) → GeomDRSub.IsDRSubmodular f →
          K ⊆ GeomDRSub.cube n → K.Nonempty → IsCompact K → Convex ℝ K →
          GeomDRSub.IsDownClosed K →
          O.val = f → O.grad = GeomDRSub.gradQ f → FTPLLinBandit.IsArgmaxSel K O.lmo →
          (∀ ω, ∃ k y, A ω (transcript A O ω k) = Sum.inr y ∧ y ∈ K ∧
            (lmoCount (transcript A O ω k) : ℝ) ≤ C * (n + n ^ 6 / ε ^ 8) ∧
            (objCount (transcript A O ω k) : ℝ) ≤ C * (1 + n ^ 6 / ε ^ 8) ∧
            projCount (transcript A O ω k) = 0 ∧
            CubeQueries (transcript A O ω k)) ∧
          Integrable (fun ω => f (result A O ω)) P ∧
          (alpha0 - ε) * sSup (f '' K) ≤ ∫ ω, f (result A O ω) ∂P) ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (A : Strategy n Ω),
        IsProbabilityMeasure P ∧
        ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ) (K : Set (EuclideanSpace ℝ (Fin n)))
          (O : Oracles n),
          (∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) → GeomDRSub.IsDRSubmodular f →
          K ⊆ GeomDRSub.cube n → K.Nonempty → IsCompact K → Convex ℝ K →
          GeomDRSub.IsDownClosed K →
          O.val = f → O.grad = GeomDRSub.gradQ f → FTPLLinBandit.IsArgmaxSel K O.lmo →
          (∀ v, OrabonaOL.OGD.IsEuclideanProj (KW K) v (O.proj v)) →
          (∀ ω, ∃ k y, A ω (transcript A O ω k) = Sum.inr y ∧ y ∈ K ∧
            lmoCount (transcript A O ω k) ≤ n ∧
            (projCount (transcript A O ω k) : ℝ) ≤ C * (n ^ 3 / ε ^ 4) ∧
            (objCount (transcript A O ω k) : ℝ) ≤ C * (1 + n ^ 3 / ε ^ 4) ∧
            CubeQueries (transcript A O ω k)) ∧
          Integrable (fun ω => f (result A O ω)) P ∧
          (alpha0 - ε) * sSup (f '' K) ≤ ∫ ω, f (result A O ω) ∂P) := by sorry

end DRSub4633.Supplement
