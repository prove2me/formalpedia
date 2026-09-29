-- Prove2me | Theorems.Thm_AutomorphicForm_exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
-- name    : AutomorphicForm.exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.444828+00:00
-- url     : https://prove2.me/theorems/33579e80-aba4-54dc-9827-7d3317f7b4e5
-- title:
--   Twisted weight asymptotics for the family σ-u
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ finite and Galois, let $\sigma\in\mathrm{Gal}(L/K)$ be such that every $K$-automorphism of $L$ lies in the subgroup of integer powers of $\sigma$, and let $v$ be a height-one prime of $\mathcal O_K$. Write $E=L\otimes_K K_v$ for the base change to the $v$-adic completion, equipped with a Borel measurable structure and an additive Haar measure $\nu$, and put $n=[L:K]$. Let $Z\subseteq E$ be compact and $Q_c\subseteq E^{\times}$ compact. The assertion is twofold. First, $z\mapsto\log\|\mathrm{Tr}_{E/K_v}(z)\|$ is integrable on $Z$ with respect to $\nu$. Second, there exist a real constant $C$ and a neighbourhood $U$ of $1$ in $K_v^{\times}$ such that for every $u\in U$ with $u^{n}\neq 1$, every $q\in Q_c$ and every measurable $g:E\to\mathbb C$ with $\|g(z)\|\le 1$ for all $z$ and $g$ vanishing off $Z$, the following hold. (a) The difference between $$\|1-u^{n}\|\int_E g\bigl((\sigma\otimes\mathrm{id})\eta-(1\otimes u)\eta\bigr)\Bigl(W\bigl(\tfrac{1\ \ q\eta}{0\ \ 1}\bigr)+2n\log\|1-u^{n}\|\Bigr)\,d\nu(\eta)$$ and $$\int_E g(z)\bigl(2\log\|N_{E/K_v}(q)\|+2n\log\|\mathrm{Tr}_{E/K_v}(z)\|\bigr)\,d\nu(z)$$ has absolute value at most $C\,\|1-u^{n}\|\,\bigl(1+|\log\|1-u^{n}\||\bigr)$; here $W$ denotes the semi-local weight, the finite sum over the extensions $w$ of $v$ to $\mathcal O_L$ of the local weight $2\log\bigl(\max(\|x_{00}\|,\|x_{01}\|)\cdot\mathrm{rowMaxNorm}(x)/\|\det x\|\bigr)$ of the $w$-component of the unipotent matrix with upper-right entry $q\eta$. (b) $\|1-u^{n}\|\int_E g\bigl((\sigma\otimes\mathrm{id})\eta-(1\otimes u)\eta\bigr)\,d\nu(\eta)=\int_E g\,d\nu$.
--
--   This is the local analysis, at a finite place $v$ of $K$, of the twisted weighted orbital integral for the scalar family $\eta\mapsto\sigma\eta-u\eta$ as $u$ tends to the degenerate locus $u^{[L:K]}=1$: the weight contribution has the explicit limiting kernel $2\log\|N(q)\|+2[L:K]\log\|\mathrm{Tr}\,z\|$, with an error of size $O(\|1-u^{n}\|(1+|\log\|1-u^{n}\||))$, uniformly in the test function and in the torus parameter $q$. It is used in the comparison of weighted twisted orbital integrals for diagonal torus elements in the base-change argument for $\mathrm{GL}_2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le.lean

import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions Classical

theorem AutomorphicForm.exists_forall_norm_mul_integral_comp_sigmaTensor_sub_smul_mul_semiLocalWeight_add_sub_integral_mul_log_norm_trace_le
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (v : HeightOneSpectrum (𝓞 K))
    [MeasurableSpace (L ⊗[K] v.adicCompletion K)] [BorelSpace (L ⊗[K] v.adicCompletion K)]
    (ν : Measure (L ⊗[K] v.adicCompletion K)) [ν.IsAddHaarMeasure]
    (Z : Set (L ⊗[K] v.adicCompletion K)) (hZ : IsCompact Z)
    (Qc : Set (L ⊗[K] v.adicCompletion K)ˣ) (hQc : IsCompact Qc) :
    IntegrableOn (fun z : (L ⊗[K] v.adicCompletion K) => Real.log ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖) Z ν ∧
    ∃ C : ℝ, ∃ U ∈ nhds (1 : (v.adicCompletion K)ˣ),
      ∀ u : (v.adicCompletion K)ˣ, u ∈ U → u ^ Module.finrank K L ≠ 1 → ∀ q : (L ⊗[K] v.adicCompletion K)ˣ, q ∈ Qc →
      ∀ g : (L ⊗[K] v.adicCompletion K) → ℂ, Measurable g → (∀ z, ‖g z‖ ≤ 1) → (∀ z, z ∉ Z → g z = 0) →
        ‖(‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ : ℂ) *
            ∫ η : (L ⊗[K] v.adicCompletion K), g (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ η -
                (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : (v.adicCompletion K)) : (L ⊗[K] v.adicCompletion K)) * η) *
              ((AutomorphicForm.semiLocalWeight K L v (AutomorphicForm.unipotentGL2 (((q : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)) * η)) +
                  2 * (Module.finrank K L : ℝ) * Real.log ‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ : ℝ) : ℂ) ∂ν -
          ∫ z : (L ⊗[K] v.adicCompletion K), g z *
              ((2 * Real.log ‖Algebra.norm (v.adicCompletion K) (((q : (L ⊗[K] v.adicCompletion K)ˣ) : (L ⊗[K] v.adicCompletion K)))‖ +
                  2 * (Module.finrank K L : ℝ) * Real.log ‖Algebra.trace (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) z‖ : ℝ) : ℂ) ∂ν‖ ≤
          C * ‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ * (1 + |Real.log ‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖|) ∧
        (‖(1 : (v.adicCompletion K)) - (((u ^ Module.finrank K L : (v.adicCompletion K)ˣ)) : (v.adicCompletion K))‖ : ℂ) * ∫ η : (L ⊗[K] v.adicCompletion K), g (AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ η -
                (Algebra.TensorProduct.includeRight (R := K) (A := L) (u : (v.adicCompletion K)) : (L ⊗[K] v.adicCompletion K)) * η) ∂ν = ∫ z : (L ⊗[K] v.adicCompletion K), g z ∂ν := by sorry
