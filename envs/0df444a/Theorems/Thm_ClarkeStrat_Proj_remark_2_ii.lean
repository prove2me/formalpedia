-- Prove2me | Theorems.Thm_ClarkeStrat_Proj_remark_2_ii
-- name    : ClarkeStrat.Proj.remark_2_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:21.534172+00:00
-- url     : https://prove2.me/theorems/31800f57-515e-4df5-a4ff-645c5255c486
-- title:
--   Remark 2 (ii), p. 559 — 0 ∈ ∂^∞f(x) for every x ∈ dom f
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$ be lower semicontinuous. Then for every $x\in\operatorname{dom} f$,
--
--   $$0\in\partial^\infty f(x),$$
--
--   where $\partial^\infty f$ is the singular limiting subdifferential (5). The reason given on the page is that the domain of the Fréchet subdifferential is dense in $\operatorname{dom} f$ (Rockafellar–Wets, *Variational Analysis*, Corollary 8.10), with function values converging.
--
--   The fact makes the singular subdifferential nonempty on the domain; it turns the inclusion $\operatorname{Proj}_{T_xX_x}\partial^\infty f(x)\subset\{0\}$ of (12) into the equality of (9).
--
--   **Formalization Note** $f$ takes values in `EReal` and is never $-\infty$. No stratification is assumed. Lower semicontinuity is necessary: the density of $\operatorname{dom}\hat\partial f$ with $f(x_k)\to f(x)$ is a statement about lower semicontinuous functions.
-- source:
--   Bolte, Daniilidis, Lewis & Shiota, Clarke subgradients of stratifiable functions, SIAM J. Optim. 18(2) (2007), https://doi.org/10.1137/060670080, p. 559, Remark 2 (ii)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ClarkeStrat_Proj_Setting
open Filter Topology
open scoped Pointwise InnerProductSpace
open NonconvexSplitting.Shared ProjLikeRetr.Retractor

namespace ClarkeStrat.Proj

/-- Remark 2 (ii), p. 559: for a lower semicontinuous `f`, `0 ∈ ∂^∞f(x)` for all `x ∈ dom f`. -/
theorem remark_2_ii {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hbot : ∀ x, f x ≠ ⊥)
    (hlsc : LowerSemicontinuous f) :
    ∀ x, f x ≠ ⊤ → (0 : EuclideanSpace ℝ (Fin n)) ∈ SingularSubdiff f x := by sorry

end ClarkeStrat.Proj
