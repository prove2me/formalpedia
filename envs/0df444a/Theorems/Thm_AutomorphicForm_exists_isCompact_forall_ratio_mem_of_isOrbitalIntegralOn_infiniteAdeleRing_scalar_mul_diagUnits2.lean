-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/dd705938-b2ef-576e-a5e7-9c639afee6f0
-- title:
--   Compact support of archimedean orbital values in the ratio a
-- statement:
--   Let $K$ be a number field, write $K_\infty$ for its infinite adele ring, and equip $\mathrm{GL}_2(K_\infty)$ with the Borel $\sigma$-algebra of its topology (the measurable structure [`AutomorphicForm.glBorelOf`](def/AutomorphicForm_TwistedOrbital.html#L57)). Let $\nu$ be a measure on $\mathrm{GL}_2(K_\infty)$ for that $\sigma$-algebra and let $f_\infty \colon \mathrm{GL}_2(K_\infty) \to \mathbb{C}$ have compact support. Then there is a compact set $C \subseteq K_\infty^\times$ with the following property: for all $a, b \in K_\infty^\times$, writing $\gamma = b \cdot \mathrm{diag}(a,1)$ for the product of the scalar matrix $b$ with the diagonal unit matrix `diagUnits2 a 1`, for every measure $\tau$ on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_\infty)$ (Borel $\sigma$-algebra) and every $J \in \mathbb{C}$, if $J$ is an orbital-integral value of $f_\infty$ at $\gamma$ relative to $(\nu, \tau)$ — that is, if there is a non-negative measurable compactly supported weight $w$ on $\mathrm{GL}_2(K_\infty)$ with $\int_{Z_\gamma} w(tx)\,d\tau(t) = 1$ for every $x$ with $f_\infty(x^{-1}\gamma x) \neq 0$, and $J = \int f_\infty(x^{-1}\gamma x)\,w(x)\,d\nu(x)$ — and if moreover $J \neq 0$, then $a \in C$. The compact set depends only on $K$, $\nu$ and $f_\infty$, uniformly in $b$, $\tau$ and $w$; no Haar or regularity hypothesis on $\nu$ or $\tau$ is imposed, and $a = 1$ is not excluded.
--
--   This is the archimedean support bound for orbital integrals along the split torus: a non-vanishing orbital value at $b\,\mathrm{diag}(a,1)$ forces some conjugate to meet the compact support of the test function, and the conjugation invariant $\mathrm{tr}^2/\det = a + 2 + a^{-1}$, which is independent of $b$, then confines the ratio $a$ to a compact annulus in $K_\infty^\times$. It feeds the finiteness statement [`AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem`](thm.html#AutomorphicForm.exists_finset_forall_window_product_eq_zero_of_not_mem), where it supplies the archimedean half of the constraint cutting the global torus sum down to finitely many terms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_ratio_mem_of_isOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_ratio_mem_of_isOrbitalIntegralOn_infiniteAdeleRing_scalar_mul_diagUnits2
    (K : Type) [Field K] [NumberField K]
    (ν : @Measure (GL (Fin 2) (InfiniteAdeleRing K)) (AutomorphicForm.glBorelOf (InfiniteAdeleRing K)))
    (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ) (hfa : HasCompactSupport fa) :
    ∃ C : Set (InfiniteAdeleRing K)ˣ, IsCompact C ∧
      ∀ (a b : (InfiniteAdeleRing K)ˣ)
        (τ : Measure (Subgroup.centralizer
            ({Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1} : Set (GL (Fin 2) (InfiniteAdeleRing K)))))
        (J : ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (InfiniteAdeleRing K) ν
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) τ fa J → J ≠ 0 → a ∈ C := by sorry
