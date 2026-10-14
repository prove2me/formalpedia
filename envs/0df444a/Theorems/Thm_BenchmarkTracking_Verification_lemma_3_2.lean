-- Prove2me | Theorems.Thm_BenchmarkTracking_Verification_lemma_3_2
-- name    : BenchmarkTracking.Verification.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:11.262177+00:00
-- url     : https://prove2.me/theorems/1ad94f46-f12d-4ea3-8827-8c9e076202ae
-- title:
--   Lemma 3.2 — $l$ solves the Neumann problem (3.8) and equals the explicit form (3.9)
-- statement:
--   Let the model parameters satisfy the standing assumptions, and let the discount rate satisfy
--   $$
--   \rho>\frac{\alpha^2|p|}{2(1-p)}+\mu_Z,\qquad \rho>\frac{\alpha^2p}{2(1-p)},\qquad \mu_Z>\kappa_2 .
--   $$
--   On any probability space carrying three independent standard Brownian motions $B^0,B^1,B^2$, let $l(r,z)$ be the sum of the first two terms of the representation (3.1),
--   $$
--   l(r,z)=\frac{1-p}p\beta^{-\frac p{1-p}}\mathbb E\Big[\int_0^\infty e^{-\rho s+\frac p{1-p}R^r_s}ds\Big]+\beta(\kappa_2-\mu_Z)\mathbb E\Big[\int_0^\infty e^{-\rho s-R^r_s}N^z_s\,ds\Big].
--   $$
--   Then:
--
--   1. both expectations are finite for every $(r,z)\in\mathbb R^2_+$;
--   2. $l$ is a classical solution of the Neumann problem (3.8) on $\mathbb R^2_+$, with $l_r(0,z)=0$;
--   3. the constant $\ell$ of (3.12) is positive, and for all $(r,z)\in\mathbb R^2_+$
--   $$
--   l(r,z)=C_1\beta^{-\frac p{1-p}}e^{\frac p{1-p}r}+C_2\beta e^{-r}+z\Big(\beta e^{-r}-\frac\beta\ell e^{-\ell r}\Big),
--   $$
--   with $C_1,C_2$ of (3.10).
--
--   This gives the first two terms of $v$ in closed form; it is used for the regularity and the convexity of $\hat u$ in Theorem 3.1 and for the bounds on the feedback control in the proof of Theorem 4.1.
--
--   **Formalization Note** The lemma prints only $\rho>\frac{\alpha^2|p|}{2(1-p)}+\mu_Z$ and $\mu_Z>\kappa_2$. When $\mu_Z<0$ this does not imply $\rho>\frac{\alpha^2p}{2(1-p)}$, and without the latter the first expectation is infinite (e.g. $d=1$, $\mu=2$, $\sigma=1$, $\eta=-1$, $\sigma_Z=10$, $\mu_Z=-10$, $p=\tfrac12$, $\rho=0.1$: then $\mathbb E[e^{R^r_s}]\ge e^{r+3.9s}$), so the explicit form (3.9) with $C_1,C_2$ of (3.10) fails. The condition $\rho>\frac{\alpha^2p}{2(1-p)}$, which Theorem 3.1 states and which makes the denominators of $C_1,C_2$ positive, is therefore added. The paper also says "$C_1,C_2>0$"; this fails for $p<0$ (then $C_1<0$) and is not formalized. The uniqueness sentence "On the other hand, …" of the lemma is not part of this statement. The statement holds on every probability space carrying the Brownian motions.
-- source:
--   Bo, Huang & Yu, Stochastic control problems with state-reflections arising from relaxed benchmark tracking, arXiv:2302.08302v4, pp. 9–10, Lemma 3.2 (3.7)–(3.12)

import Mathlib
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_BenchmarkTracking_Verification_Model
import Definitions.Def_BenchmarkTracking_Verification_Analysis
import Definitions.Def_BenchmarkTracking_Verification_Representation
import Definitions.Def_BenchmarkTracking_Verification_PDE

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BenchmarkTracking.Verification

theorem lemma_3_2 {d : ℕ} (M : Params d) (hM : M.Standing) (ρ : ℝ) (hρ0 : 0 < ρ)
    (hρp : M.alpha ^ 2 * M.p / (2 * (1 - M.p)) < ρ)
    (hρ : M.alpha ^ 2 * |M.p| / (2 * (1 - M.p)) + M.muZ < ρ) (hZ : M.kappa2 < M.muZ)
    {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin 3)) (hB : EthierKurtz.IsStandardBrownian Pr B) :
    (∀ r z : ℝ, 0 ≤ r → 0 ≤ z → expect1 M ρ Pr B r < ∞ ∧ expect2 M ρ Pr B r z < ∞) ∧
    IsClassicalSol38 M ρ (lRep M ρ Pr B) ∧
    0 < M.ell ρ ∧
    ∀ r z : ℝ, 0 ≤ r → 0 ≤ z →
      lRep M ρ Pr B r z =
        M.C1 ρ * M.beta ^ (-M.p / (1 - M.p)) * Real.exp (M.p / (1 - M.p) * r) +
          M.C2 ρ * M.beta * Real.exp (-r) +
          z * (M.beta * Real.exp (-r) - M.beta / M.ell ρ * Real.exp (-(M.ell ρ * r))) := by sorry

end BenchmarkTracking.Verification
