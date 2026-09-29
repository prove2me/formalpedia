-- Prove2me | Theorems.Thm_AutomorphicForm_exists_nhds_forall_exists_normString_diagUnits2_eq_toTensorGL_iff_of_norm_sub_le
-- name    : AutomorphicForm.exists_nhds_forall_exists_normString_diagUnits2_eq_toTensorGL_iff_of_norm_sub_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/0d16c3de-8d45-5e0e-82d2-08cd6869d398
-- title:
--   Local constancy of diagonal norm-string lifts near t=1
-- statement:
--   Let $K$ and $L$ be number fields with $L$ a finite Galois extension of $K$, and let $\sigma$ be an element of $\mathrm{Gal}(L/K)$ such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$. Let $v$ be a nonzero prime of $\mathcal{O}_K$, write $K_v$ for the $v$-adic completion of $K$ and set $E = L \otimes_K K_v$. The assertion is that there exist a set $U$ in the neighbourhood filter of $1$ in $K_v^\times$ and a real $\rho > 0$ such that for all $a, a', t, t' \in K_v^\times$ with $t \in U$, $\|a' - a\| \le \rho\|a\|$ and $\|t' - t\| \le \rho\|1 - t\|$ (norms taken in $K_v$), the following two conditions are equivalent: there exist $\alpha, \beta \in E^\times$ with $\delta \cdot \sigma(\delta) \cdots \sigma^{\ell-1}(\delta) = \mathrm{diag}(a, at)$, where $\delta = \mathrm{diag}(\alpha,\beta) \in \mathrm{GL}_2(E)$, $\ell = [L:K]$, $\sigma$ acts on $\mathrm{GL}_2(E)$ entrywise through $\sigma \otimes \mathrm{id}$ and $\mathrm{diag}(a,at)$ is viewed in $\mathrm{GL}_2(E)$ via $x \mapsto 1 \otimes x$; and the same condition with $(a, at)$ replaced by $(a', a't')$.
--
--   This is the local constancy, on the cells $\|a'-a\| \le \rho\|a\|$, $\|t'-t\| \le \rho\|1-t\|$ with $t$ near $1$, of the condition that a diagonal torus element $\mathrm{diag}(a,at)$ admit a diagonal twisted-norm ($\sigma$-norm) preimage in $\mathrm{GL}_2(L \otimes_K K_v)$; by the characterisation of that condition as membership of $a$ and $at$ in the norm subgroup $N(E^\times)$, which contains $\ell$-th powers and hence a neighbourhood of $1$, the condition depends only on the cell. It is used in the local analysis of twisted orbital integrals and matching feeding the base-change comparison behind the Langlands–Tunnell input.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_nhds_forall_exists_normString_diagUnits2_eq_toTensorGL_iff_of_norm_sub_le.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct
open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.exists_nhds_forall_exists_normString_diagUnits2_eq_toTensorGL_iff_of_norm_sub_le
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ), ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a a' t t' : (v.adicCompletion K)ˣ, t ∈ U →
        ‖(a' : (v.adicCompletion K)) - (a : (v.adicCompletion K))‖ ≤ ρ * ‖(a : (v.adicCompletion K))‖ →
        ‖(t' : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ ≤ ρ * ‖(1 : (v.adicCompletion K)) - (t : (v.adicCompletion K))‖ →
        ((∃ α β : (L ⊗[K] (v.adicCompletion K))ˣ, AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a (a * t))) ↔
          (∃ α β : (L ⊗[K] (v.adicCompletion K))ˣ, AutomorphicForm.normString K L (v.adicCompletion K) σ (diagUnits2 α β) =
                AutomorphicForm.toTensorGL K L (v.adicCompletion K) (diagUnits2 a' (a' * t')))) := by sorry
