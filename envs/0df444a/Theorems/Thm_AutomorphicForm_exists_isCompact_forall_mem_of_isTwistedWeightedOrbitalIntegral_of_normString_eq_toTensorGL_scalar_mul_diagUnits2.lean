-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
-- name    : AutomorphicForm.exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/2e32fb4d-761f-50e9-8abe-a884a84a2f7c
-- title:
--   Compactness of the split parameter for nonvanishing twisted weighted orbital integrals
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a $K$-algebra, let $\sigma$ be a $K$-algebra automorphism of $L$, let $v$ be a height-one prime of $\mathcal{O}_K$ with completion $K_v :=$ `v.adicCompletion K`, and put $E_v := L \otimes_K K_v$. Fix a unit $a \in K_v^\times$ and a function $\varphi_v : \mathrm{GL}_2(E_v) \to \mathbb{C}$ which is locally constant and has compact support. The assertion is that there exists a compact set $C \subseteq K_v^\times$ with the following property: for every $b \in K_v^\times$ and every $\delta \in \mathrm{GL}_2(E_v)$ whose norm string $\prod_{i=0}^{[L:K]-1} \sigma^{i}(\delta)$ — the ordered product of the iterates of $\delta$ under the automorphism of $\mathrm{GL}_2(E_v)$ induced by $\sigma \otimes \mathrm{id}$ — equals the image in $\mathrm{GL}_2(E_v)$, under the map induced by $x \mapsto 1 \otimes x$, of the scalar matrix $b \cdot I$ times $\mathrm{diag}(a,1)$, and for every measure $\tau'$ on the $\sigma$-twisted centraliser $\{t : t\delta\sigma(t)^{-1} = \delta\}$ of $\delta$ (with its Borel structure) and every $J \in \mathbb{C}$ such that $J$ is a value of the twisted weighted orbital integral of $\varphi_v$ at $(\delta,\tau')$ — that is, there is a function $s$ on $\mathrm{GL}_2(E_v)$ satisfying the predicate `IsTwistedSectionFnOn` for these data and $J = \int \varphi_v(x^{-1}\delta\sigma(x))\, w(x)\, s(x)$ against the semi-local Haar measure, where $w(x)$ is the sum over the extensions $w$ of $v$ to $\mathcal{O}_L$ of the local weights of the place components of $x$ — one has: if $J \neq 0$ then $b \in C$.
--
--   This is the compact-support half of a finite twisted-weighted window along the split family $b \mapsto b\cdot\mathrm{diag}(a,1)$: nonvanishing of a twisted weighted orbital integral of a locally constant compactly supported semi-local test function confines the scalar parameter $b$ to a fixed compact subset of $K_v^\times$, independently of $\delta$, of the measure on the twisted centraliser and of the chosen section function. It is used in the construction of a locally constant, compactly supported function on the units recording these orbital-integral values at the split family.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain

attribute [local instance] AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isCompact_forall_mem_of_isTwistedWeightedOrbitalIntegral_of_normString_eq_toTensorGL_scalar_mul_diagUnits2
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K)) (a : (v.adicCompletion K)ˣ)
    (φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ) (hφv : AutomorphicForm.IsSemiLocalTestFn K L v φv) :
    ∃ C : Set (v.adicCompletion K)ˣ, IsCompact C ∧
      ∀ (b : (v.adicCompletion K)ˣ) (δ : GL (Fin 2) (L ⊗[K] v.adicCompletion K)),
        AutomorphicForm.normString K L (v.adicCompletion K) σ δ =
          AutomorphicForm.toTensorGL K L (v.adicCompletion K)
            (Matrix.GeneralLinearGroup.scalar (Fin 2) b * diagUnits2 a 1) →
        ∀ (τ' : Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ)) (J : ℂ),
          AutomorphicForm.IsTwistedWeightedOrbitalIntegral K L v σ δ τ' φv J → J ≠ 0 → b ∈ C := by sorry
