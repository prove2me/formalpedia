-- Prove2me | Theorems.Thm_DRSub4633_lemma_4_3
-- name    : DRSub4633.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:04:52.09621+00:00
-- url     : https://prove2.me/theorems/57758890-2b69-48f1-bc78-18b6b3b6d115
-- title:
--   Lemma 4.3 — affine normalization
-- statement:
--   Let $f$ be nonnegative, continuously differentiable and DR-submodular on $Q=[0,1]^n$, and fix a state $x\in Q$. Let $d$ be the chain increments, $\ell(z)=f(0)+\langle d,z\rangle$ the affine normalizer and $F=f-\ell$ the residual of (11). Then $F$ is nonnegative and DR-submodular on $Q$,
--   $$F(0)=F(0_S,1_L)=F(1)=0,\qquad \ell(h(x))\ge\alpha_0\,\ell(x).$$
--   Here $(0_S,1_L)$ is the point with zeros on the small coordinates $x_j\le s$ and ones on the large ones.
--
--   The normalization reduces the comparison to the residual $F$, which has the boundary zeros used in every later comparison.
--
--   Differences from the source:
--   - encoding: objective defined on Q only; R^n with coordinatewise order; C^1 with boundary derivatives the continuous extensions of interior ones → f a total function on EuclideanSpace ℝ (Fin n), hypotheses on the cube only, values off the cube never read; the order written coordinatewise; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, fderivWithin the cube); reason: Lean convention; on the cube the within-cube derivative of a C^1 function is the continuous extension of the interior derivative, so the instances are the same
--   - encoding: L includes a dummy coordinate of state 1, label 1, weight q = 1, zero field component → only the original coordinates are represented; the dummy enters as label 1 with q_1 = 1 and its zero terms are dropped; reason: F does not depend on the dummy coordinate (p.10), so every dropped term is zero; same instances
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 4.3, p.14

import Mathlib
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_DRSub4633_resid
import Definitions.Def_DRSub4633_affNorm
import Definitions.Def_DRSub4633_mergePt
import Definitions.Def_DRSub4633_hRec
import Definitions.Def_DRSub4633_alpha0

namespace DRSub4633

/-- **Lemma 4.3 (Affine normalization).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 4.3, p.14: "The function `F` in (11) is
nonnegative and DR-submodular on `Q`, and `F(0) = F(0_S, 1_L) = F(1) = 0`, `ℓ(h(x)) ≥ α₀ℓ(x)`."

Standing hypotheses (Sections 3.1 and 4.1, pp.7–10): `f` nonnegative, `C¹` and DR-submodular on
`Q = [0, 1]^n`; `x ∈ Q` is the fixed state defining the order `π`, the increments `d`, the
normalizer `ℓ` and the residual `F = f − ℓ`.

**Formalization Note.** `(0_S, 1_L)` is `mergePt x 0 1`: zero on the small coordinates
`x_j ≤ s` and one on the large ones. -/
theorem lemma_4_3 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : ∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) (hf : GeomDRSub.IsDRSubmodular f)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ GeomDRSub.cube n) :
    (∀ z ∈ GeomDRSub.cube n, 0 ≤ resid f x z) ∧ GeomDRSub.IsDRSubmodular (resid f x) ∧
    resid f x 0 = 0 ∧ resid f x (mergePt x (fun _ => 0) (fun _ => 1)) = 0 ∧
    resid f x (WithLp.toLp 2 (fun _ => (1 : ℝ))) = 0 ∧
    alpha0 * affNorm f x x ≤ affNorm f x (hRec x) := by sorry

end DRSub4633
