-- Prove2me | Theorems.Thm_AutomorphicForm_isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
-- name    : AutomorphicForm.isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/0e969262-3ff1-5fd4-9048-830fe50359e0
-- title:
--   Diagonal twisted resolvent: units, cocycle relation, norm identity
-- statement:
--   Let $K \subseteq L$ be number fields with $L/K$ Galois, and let $D$ consist of a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ of $L$, each continuous and each extending the corresponding automorphism of $L$ along $L \to \mathbb{A}_L$. Fix $\sigma \in \mathrm{Gal}(L/K)$ such that every $\tau$ lies in the subgroup of integer powers of $\sigma$, a matrix $t \in \mathrm{GL}_2(L)$ with $t_{10} = t_{01} = 0$, an element $b \in \mathrm{GL}_2(\mathbb{A}_L)$ with $b_{10} = 0$, a unit $z \in \mathbb{A}_L^{\times}$, and adeles $A, B, E$ equal respectively to the $(0,0)$, $(1,1)$ and $(0,1)$ entries of $b^{-1} \cdot t \cdot (D.\mathrm{act}\,\sigma)(z \cdot b)$, where $t$ is mapped entrywise into $\mathbb{A}_L$, $z$ enters as the scalar matrix $z I$, and $D.\mathrm{act}\,\sigma$ is applied entrywise. Then: $A$ and $B$ are units; writing $x = b_{01} \cdot b_{00}^{-1}$ (the entry $b_{00}$ being a unit of $\mathbb{A}_L$ since $b_{10} = 0$), one has $A \cdot (D.\mathrm{act}\,\sigma)(x) = B \cdot x + E$; moreover $\prod_{i < [L:K]} (D.\mathrm{act}\,\sigma)^{i}(B)$ equals the image in $\mathbb{A}_L$ of $N_{L/K}(t_{11}/t_{00}) \in K$ times $\prod_{i < [L:K]} (D.\mathrm{act}\,\sigma)^{i}(A)$; and $(D.\mathrm{act}\,\sigma)^{[L:K]}$ fixes every adele.
--
--   This is the Iwasawa-coordinate computation for the twisted resolvent $b^{-1} t\,\sigma_D(zb)$ attached to a diagonal $t$ and a Borel element $b$: it records that the diagonal entries are idelic units, that the unipotent coordinate $x = b_{01}/b_{00}$ satisfies a twisted affine relation, and that the telescoping product of the ratios $B/A$ over a full $\sigma$-orbit is the norm of $t_{11}/t_{00}$. It feeds the excursion and height estimates for adelic automorphic forms proved in [`AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero`](thm.html#AutomorphicForm.exists_forall_abs_log_adelicHeight_mul_adelicHeight_adelicWeyl_le_mul_prod_pow_log_measure_of_doubleCoset_apply_ne_zero) and [`AutomorphicForm.exists_forall_norm_div_mem_unitBox_of_lintegral_orbital_doubleCoset_ne_zero`](thm.html#AutomorphicForm.exists_forall_norm_div_mem_unitBox_of_lintegral_orbital_doubleCoset_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_HaarQuotient
import Definitions.Def_AutomorphicForm_BorelSubgroup
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open IsDedekindDomain
open scoped TensorProduct Pointwise ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.glBorel

open scoped TensorProduct.RightActions in

theorem AutomorphicForm.isUnit_and_mul_act_eq_add_and_prod_iterate_act_eq_norm_mul_of_mem_adelicBorel_of_diagonal
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (t : GL (Fin 2) L) (ht₁ : (t : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) (ht₂ : (t : Matrix (Fin 2) (Fin 2) L) 0 1 = 0)
    (b : AdelicGL2 (𝓞 L) L) (hb : b ∈ AutomorphicForm.adelicBorel (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ)
    (A B E : AdeleRing (𝓞 L) L)
    (hA : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 0 = A)
    (hB : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 1 1 = B)
    (hE : ((b⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L t *
            AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * b) : AdelicGL2 (𝓞 L) L) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 = E) :
    (IsUnit A ∧ IsUnit B) ∧
    A * (D.act σ) ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
              ((AutomorphicForm.borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 L) L)ˣ)) =
      B * ((b : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 L) L)) 0 1 *
              ((AutomorphicForm.borelDiagFst ⟨b, hb⟩)⁻¹ : (AdeleRing (𝓞 L) L)ˣ)) + E ∧
    (∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] B =
      algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L
        (Algebra.norm K ((t : Matrix (Fin 2) (Fin 2) L) 1 1 / (t : Matrix (Fin 2) (Fin 2) L) 0 0))) *
      ∏ i ∈ Finset.range (Module.finrank K L), (⇑(D.act σ))^[i] A) ∧
    (∀ r : AdeleRing (𝓞 L) L, (⇑(D.act σ))^[Module.finrank K L] r = r) := by sorry
