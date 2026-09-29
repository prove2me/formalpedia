-- Prove2me | Theorems.Thm_AutomorphicForm_semiLocalComponent_glFin_inv_mul_unipotentGL2_mul_diagOne_mul_centralScalar_mul_sigmaAdelicAct
-- name    : AutomorphicForm.semiLocalComponent_glFin_inv_mul_unipotentGL2_mul_diagOne_mul_centralScalar_mul_sigmaAdelicAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.104682+00:00
-- url     : https://prove2.me/theorems/0c1c95dd-a898-546a-b129-6e94668e19fd
-- title:
--   Semi-local component above v of a twisted unipotent product
-- statement:
--   Let $K\subseteq L$ be number fields with $L/K$ Galois, let $D$ be an `IdeleGaloisDescent` datum for $L/K$, i.e. a monoid homomorphism $\sigma\mapsto D.\mathrm{act}\,\sigma$ from $\mathrm{Gal}(L/K)$ to the ring automorphisms of $\mathbb{A}_L$ that is continuous in each $\sigma$ and restricts to $\sigma$ on the image of $L$; fix $\sigma\in\mathrm{Gal}(L/K)$, a nonzero prime $v$ of $\mathcal{O}_K$, units $t,\zeta\in\mathbb{A}_L^\times$, an element $k\in GL_2(\mathbb{A}_L)$ and an adele $x\in\mathbb{A}_L$. Write $\hat\sigma=\sigma\otimes 1$ for the induced automorphism of $L\otimes_K K_v$, and for $u\in\mathbb{A}_L^\times$ let $u_v\in(L\otimes_K K_v)^\times$ be the image of the finite part of $u$ under the isomorphism $\mathbb{A}_{L,\mathrm{fin}}\to\prod_{w\mid v}L_w\cong L\otimes_K K_v$ (the map `semiLocalEval`), and likewise $x_v$ for the finite part of $x$; applying `semiLocalEval` entrywise sends $GL_2(\mathbb{A}_{L,\mathrm{fin}})$ to $GL_2(L\otimes_K K_v)$. Then the image in $GL_2(L\otimes_K K_v)$ of the finite part of $$k^{-1}\begin{pmatrix}1&xt^{-1}\\0&1\end{pmatrix}\begin{pmatrix}(D.\mathrm{act}\,\sigma)(t)\,t^{-1}&0\\0&1\end{pmatrix}\,(D.\mathrm{act}\,\sigma)(\zeta)I_2\,(D.\mathrm{act}\,\sigma)(k)$$ equals $$k_v^{-1}\begin{pmatrix}1&x_vt_v^{-1}\\0&1\end{pmatrix}\begin{pmatrix}\hat\sigma(t_v)t_v^{-1}&0\\0&1\end{pmatrix}\,\hat\sigma(\zeta_v)I_2\;\hat\sigma(k_v),$$ where $k_v$ denotes the semi-local component of $k$ and $\hat\sigma$ acts on $GL_2$ entrywise.
--
--   This is the place-by-place shape of the unipotent-type integrand occurring in the twisted trace formula for $GL_2$ over $L/K$: the semi-local component map is a group homomorphism, it carries unipotent, diagonal and central adelic matrices to the corresponding matrices over $L\otimes_K K_v$, and the descent action of $\sigma$ becomes $\sigma\otimes 1$ above $v$. It is used in the factorisation of the twisted orbital integral over a transversal, in [`AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram`](thm.html#AutomorphicForm.TwistedBruhat.exists_forall_integral_transversal_eq_indicator_mul_prod_unipotentOrbitalFn_unram).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_semiLocalComponent_glFin_inv_mul_unipotentGL2_mul_diagOne_mul_centralScalar_mul_sigmaAdelicAct.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem AutomorphicForm.semiLocalComponent_glFin_inv_mul_unipotentGL2_mul_diagOne_mul_centralScalar_mul_sigmaAdelicAct
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (v : HeightOneSpectrum (𝓞 K))
    (t ζ : (AdeleRing (𝓞 L) L)ˣ) (k : AutomorphicForm.AdelicGL2 (𝓞 L) L) (x : AdeleRing (𝓞 L) L) :
    AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L
        (k⁻¹ * AutomorphicForm.unipotentGL2 (x * ((t⁻¹ : (AdeleRing (𝓞 L) L)ˣ) : AdeleRing (𝓞 L) L)) *
          NumberField.AdelicLevel.diagOne (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ t * t⁻¹) *
          AutomorphicForm.centralScalar (𝓞 L) L (M4aHerbrand.IdeleGaloisDescent.unitsAct D σ ζ) *
          AutomorphicForm.sigmaAdelicAct K L D σ k)) =
      (AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L k))⁻¹ *
        TwistedUnipotentTerm.semiLocalUnipotent K L v
          (AutomorphicForm.semiLocalEval K L v x.2 *
            (((AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)⁻¹ : (L ⊗[K] v.adicCompletion K)ˣ) :
              L ⊗[K] v.adicCompletion K)) *
        NumberField.AdelicLevel.diagOne
          (Units.mapEquiv (Algebra.TensorProduct.congr σ
              (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv
            (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t) *
            (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v t)⁻¹) *
        TwistedUnipotentTerm.semiLocalCentral K L v
          (Units.mapEquiv (Algebra.TensorProduct.congr σ
              (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toMulEquiv
            (AutomorphicForm.TransversalMeasure.semiLocalIdele K L v ζ)) *
        Matrix.GeneralLinearGroup.map
          ((Algebra.TensorProduct.congr σ
            (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K)).toRingEquiv.toRingHom)
          (AutomorphicForm.semiLocalComponent K L v (NumberField.AdelicLevel.glFin (𝓞 L) L k)) := by sorry
