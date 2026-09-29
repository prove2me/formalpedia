-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one
-- name    : AutomorphicForm.SmoothCuspRealizationAt.norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/d926e3cd-38d0-54cd-8d0a-32f70bc541c8
-- title:
--   Unimodular central eigenvalues: central character has modulus the idelic norm
-- statement:
--   Let $F$ be a number field, let $D$ be an arbitrary subset of $\mathrm{GL}_2(\mathbb{A}_F)$ and $B$ an arbitrary subset of $\mathbb{A}_F$, and let $\Phi$ be a Hecke eigensystem for $F$ with values in $\mathbb{C}$, given by a nonzero level ideal of $\mathcal{O}_F$ together with families $a_v, b_v$ indexed by the finite places. Work with the carrier pins `productionPinsOf` attached to $(D,B)$: the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_F)$, centre $Z = \top$ (the full idele group $\mathbb{A}_F^\times$), level subgroups $N \mapsto \mathrm{levelOne}(N) \cap \ker(\mathrm{glArch})$, Hecke generators $v \mapsto \mathrm{heckeGen}(v)$, and on $\mathbb{A}_F$ the Borel structure with additive Haar measure conditioned on $B$. Let $R$ be a smooth cuspidal realization at these pins of the raw central rescaling $\Phi^{\mathrm{raw}}$ of $\Phi$ (same level and same $a_v$, with central eigenvalues $N(v)^{-1}b_v$, $N(v)$ the absolute norm of $v$): thus $R$ consists of a function on $\mathrm{GL}_2(\mathbb{A}_F)$ that is somewhere nonzero, a central character $\xi : \mathbb{A}_F^\times \to \mathbb{C}^\times$, the smooth cuspidal automorphy condition with this central character, invariance under right translation by the level subgroup at $\Phi.\mathrm{level}$, and, outside a finite exceptional set, Hecke coset eigenvalue $a_v$ and central eigenvalue $N(v)^{-1}b_v$. Assume $R$ is genuine, i.e. its underlying function is continuous, and that there is a finite set $S$ of finite places with $\lVert b_v\rVert = 1$ for all $v \notin S$. Then for every $z \in \mathbb{A}_F^\times$ one has $\lvert \xi(z)\rvert = \lVert z \rVert_{\mathbb{A}_F}$, the idelic norm being the module of $z$ for the additive Haar measure on $\mathbb{A}_F$.
--
--   This is the exponent-one case of the modulus theorem for the central character of a cuspidal realization: arithmetically normalised eigensystems have unimodular central eigenvalues, and after the raw rescaling the central character has modulus exactly the idelic norm, so that its twist by the inverse idelic norm is unitary. It is used in the Rankin–Selberg and converse-theorem steps of the Langlands–Tunnell input, where unitarity of the normalised central character is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem AutomorphicForm.SmoothCuspRealizationAt.norm_centralChar_eq_ideleNorm_of_forall_norm_b_eq_one
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (B : Set (AdeleRing (𝓞 F) F)) (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
      (productionPinsOf F D
        (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => NumberField.AdelicLevel.heckeGen (𝓞 F) F v) B) Φ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F
      (productionPinsOf F D
        (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => NumberField.AdelicLevel.heckeGen (𝓞 F) F v) B) Φ.toRawCentral R)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hb : ∀ v ∉ S, ‖Φ.b v‖ = 1) :
    ∀ z : (productionPinsOf F D
        (fun N => NumberField.AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => NumberField.AdelicLevel.heckeGen (𝓞 F) F v) B).Z,
      ‖((R.centralChar z : ℂˣ) : ℂ)‖
        = NumberField.TateGlobal.ideleNorm F (z : (AdeleRing (𝓞 F) F)ˣ) := by sorry
