-- Prove2me | Theorems.Thm_ChvatalOneHard398_SAT_lemma_19
-- name    : ChvatalOneHard398.SAT.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:50.054525+00:00
-- url     : https://prove2.me/theorems/be2e8f73-bba9-4c3c-a55a-5e803097d0c0
-- title:
--   Lemma 19 — affine identities and integral determination
-- statement:
--   Let $X$ be a valid functional formulation with free-variable vector $b(x)$. For any gate $g$ and affine function $\eta$ vanishing at all Boolean graph points $(v,f_g(v))$,
--
--   $$\eta(x_{I_g},x_{O_g})=0\qquad(x\in X).$$
--
--   If $x\in X$ and $b(x)$ is integral, then all of $x$ is integral, and every $y\in X$ with $b(y)=b(x)$ equals $x$. Both claims include the auxiliary weight variables. These facts provide identities on fractional points and uniqueness from integral free data.
--
--   Differences from the source:
--   - encoding: the sequential functional formulation of equation (1) → an ordered gate list, explicit shape validity, and its exact-one equations in the unit cube; reason: the unit-cube bounds on all coordinates follow from (1); gate truth tables and variable ordering express precisely the source data
-- source:
--   Alberto Del Pia, 0/1 integer programming over polytopes of Chvátal rank one is as hard as lattice problems, STOC 2027 submission #398 (October 2026), p.20, Lemma 19(a), and p.21, Lemma 19(b); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/398.pdf

import Mathlib
import Definitions.Def_ChvatalOneHard398_SAT_Functional

namespace ChvatalOneHard398.SAT
open CombOpt.ChvatalRank

theorem lemma_19 (X : Functional) (hX : X.Valid) :
    (∀ j, j < X.gates.length →
      ∀ eta : (Fin (X.gates[j]!.inputs.length + X.gates[j]!.outputs) → ℝ) →ᵃ[ℝ] ℝ,
        (∀ v < 2 ^ X.gates[j]!.inputs.length, eta (gateVertex X.gates[j]! v) = 0) →
        ∀ x ∈ functionalPoly X, eta (gateCoordinates X j x) = 0) ∧
    (∀ x ∈ functionalPoly X,
      (∀ i : Fin X.free, ∃ z : ℤ, coord x i.val = z) →
      IsIntegralVector x ∧ ∀ y ∈ functionalPoly X,
        (∀ i : Fin X.free, coord y i.val = coord x i.val) → y = x) := by sorry

end ChvatalOneHard398.SAT
