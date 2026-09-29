-- Prove2me | Theorems.Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv
-- name    : AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/23f38864-7d65-54a9-9e6e-f248a8844fe6
-- title:
--   Naturality of the trace on differentials under isomorphisms of the pair
-- statement:
--   Let $K$ be a field and let $F, F', F_0, F_0'$ be fields equipped with $K$-algebra structures. Let $\varphi' \colon F \to F'$ and $\varphi \colon F_0 \to F_0'$ be $K$-algebra homomorphisms, and let $\theta \colon F \xrightarrow{\sim} F_0$ and $\theta' \colon F' \xrightarrow{\sim} F_0'$ be $K$-algebra isomorphisms which intertwine them in the sense that $\theta'(\varphi'(x)) = \varphi(\theta(x))$ for all $x \in F$. Assume `SeparableAlong K φ'`, that is, $F'$ is a separable algebra over $F$ for the $F$-algebra structure supplied by $\varphi'$. Here, for a $K$-algebra map $\psi \colon E \to E'$ of fields, `pullbackAlong ψ` is the $K$-linear map $\Omega_{E/K} \to \Omega_{E'/K}$ induced by $\psi$ on Kähler differentials, and `traceAlong ψ` is the $K$-linear map $\Omega_{E'/K} \to \Omega_{E/K}$ defined, when $E'/E$ is separable along $\psi$ (hence formally étale, so that the base-change map $E' \otimes_E \Omega_{E/K} \to \Omega_{E'/K}$ is an isomorphism), as the inverse of that isomorphism followed by $\mathrm{Tr}_{E'/E}$ on the left tensor factor and the identification $E \otimes_E \Omega_{E/K} \cong \Omega_{E/K}$, and as $0$ otherwise. The conclusion is that for every $\eta \in \Omega_{F'/K}$ one has $\theta^{*}(\mathrm{tr}_{\varphi'}\,\eta) = \mathrm{tr}_{\varphi}(\theta'^{*}\eta)$, the pull-backs being taken along the underlying $K$-algebra homomorphisms of $\theta$ and $\theta'$.
--
--   This is the naturality of the trace (cotrace) map on differentials with respect to an isomorphism of the pair of fields: transporting a separable extension by compatible isomorphisms of base and top field transports the trace of differentials accordingly. It is used in the computations with correspondences and degeneracy maps on modular curves, where differentials are moved between function fields identified by $K$-algebra isomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_DifferentialPushPull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv
    {K F F' F₀ F₀' : Type*} [Field K] [Field F] [Field F'] [Field F₀] [Field F₀']
    [Algebra K F] [Algebra K F'] [Algebra K F₀] [Algebra K F₀']
    (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F' ≃ₐ[K] F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (hsep : AlgebraicCurve.SeparableAlong K φ') (η : Ω[F'⁄K]) :
    AlgebraicCurve.Differential.pullbackAlong (θ : F →ₐ[K] F₀) (AlgebraicCurve.Differential.traceAlong φ' η) =
      AlgebraicCurve.Differential.traceAlong φ (AlgebraicCurve.Differential.pullbackAlong (θ' : F' →ₐ[K] F₀') η) := by sorry
