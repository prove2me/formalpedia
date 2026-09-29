-- Prove2me | Theorems.Thm_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero
-- name    : AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.838273+00:00
-- url     : https://prove2.me/theorems/f77cd846-f789-581b-be02-72ac50884614
-- title:
--   Vanishing of a local test function at a scalar from nearby orbital integrals
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of its ring of integers $\mathcal O_K$, and $K_v$ the associated adic completion. Let $f_v : \mathrm{GL}_2(K_v) \to \mathbb C$ be a local test function, i.e. locally constant with compact support, and let $c \in K_v^\times$; write $z = c\cdot 1_2$ for the corresponding scalar element of $\mathrm{GL}_2(K_v)$. Assume there is a neighbourhood $U$ of $z$ with the following property: for every $\gamma \in U$ with $\det \gamma = c^2$ such that $\operatorname{tr}(\gamma)^2 - 4\det(\gamma)$ is a unit of $K_v$ (the regular semisimplicity condition used in the project), for every measure $\tau$ on the centraliser of $\{\gamma\}$ in $\mathrm{GL}_2(K_v)$, equipped with its Borel $\sigma$-algebra, which is a Haar measure, and for every $I \in \mathbb C$ admitting a weight $w : \mathrm{GL}_2(K_v) \to \mathbb R$ that is nonnegative, Borel measurable, compactly supported, satisfies $\int_{T_\gamma} w(tx)\,d\tau(t) = 1$ for all $x$ with $f_v(x^{-1}\gamma x) \neq 0$, and for which $I = \int_{\mathrm{GL}_2(K_v)} f_v(x^{-1}\gamma x)\,w(x)\,dx$ against the project's Haar measure `localHaar` on $\mathrm{GL}_2(K_v)$, one has $I = 0$. Then $f_v(z) = 0$.
--
--   This is the local vanishing statement at a central element extracted from the behaviour of orbital integrals on the nearby regular semisimple elements of the fibre $\det = c^2$, the quantitative content being Shalika's germ expansion of orbital integrals at the centre; stating the hypothesis for every Haar measure on each centraliser removes any normalisation choice. It is used in the treatment of local matching and central transfer, via [`AutomorphicForm.areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf`](thm.html#AutomorphicForm.areMatchingLocal_central_transfer_and_eq_zero_of_not_exists_isNormOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField
open IsDedekindDomain

theorem
  AutomorphicForm.apply_scalar_eq_zero_of_nhds_forall_isRegularSemisimple_isOrbitalIntegral_eq_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (hfv : AutomorphicForm.IsLocalTestFn K v fv)
    (c : (v.adicCompletion K)ˣ)
    (hvan : ∃ U ∈ nhds (Matrix.GeneralLinearGroup.scalar (Fin 2) c),
      ∀ γ ∈ U, Matrix.GeneralLinearGroup.det γ = c ^ 2 → AutomorphicForm.IsRegularSemisimple γ →
        ∀ τ : @Measure (AutomorphicForm.localCentralizer K v γ) (AutomorphicForm.localCentralizerBorel K v γ),
          @Measure.IsHaarMeasure _ _ _ (AutomorphicForm.localCentralizerBorel K v γ) τ →
            ∀ I : ℂ, AutomorphicForm.IsOrbitalIntegral K v γ τ fv I → I = 0) :
    fv (Matrix.GeneralLinearGroup.scalar (Fin 2) c) = 0 := by sorry
