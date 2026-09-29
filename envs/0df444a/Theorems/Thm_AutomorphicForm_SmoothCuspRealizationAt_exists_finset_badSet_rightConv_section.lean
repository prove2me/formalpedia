-- Prove2me | Theorems.Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_finset_badSet_rightConv_section
-- name    : AutomorphicForm.SmoothCuspRealizationAt.exists_finset_badSet_rightConv_section
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/2d4fab28-0523-5467-a301-db76782c307e
-- title:
--   A bad set for a smoothed cusp realisation, with coset data
-- statement:
--   Let $F$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_F)$, and $\Phi$ a Hecke eigensystem for $F$ with values in $\mathbb{C}$ (a nonzero level ideal together with families $a_v,b_v$). Let $R$ be a smooth cusp realisation, at the production pins built from $D$, from the level subgroups $N \mapsto \mathrm{levelOne}(N) \cap \ker(\mathrm{glArch})$, from the Hecke generators $\mathrm{heckeGen}(v)$ and from the box $\mathrm{adelicBox}(F)$, of the rescaled eigensystem `Φ.toRawCentral` (same level and same $a_v$, with $b_v$ replaced by $(\#(\mathcal{O}_F/v))^{-1}b_v$); assume its underlying function equals the right convolution $g \mapsto \int \varphi(gx)f(x)\,dx$ for functions $\varphi,f$ on $\mathrm{GL}_2(\mathbb{A}_F)$. Let $\psi$ be an additive character of $\mathbb{A}_F$ that is continuous, nontrivial and trivial on $F$, let $\chi:\mathbb{A}_F^\times \to \mathbb{C}^\times$ be a continuous homomorphism, and let $S_0$ be a finite set of finite places. Then there is a finite set $S$ of finite places containing $S_0$ and the exceptional set of $R$ such that: no $v \notin S$ divides the level of $\Phi$; $\chi$ is unramified at every $v \notin S$ (its local component is trivial on units of $\mathcal{O}_v$ with integral inverse); every idele unit $u$ with trivial archimedean component, with $u_v = 1$ for all $v \in S$, and with finite part in the group of unit ideles satisfies $\chi(u)=1$ and $\|u\|=1$; for every finite place $v$ the idele norm of the uniformiser idele at $v$ is $(\#(\mathcal{O}_F/v))^{-1}$; and for $v \notin S$ the convolution $\varphi * f$ is invariant under right translation by the image of $\mathrm{GL}_2(\mathcal{O}_v)$. Moreover there exist uniformisers $\varpi_v \in \mathcal{O}_v$ with nonzero image in $F_v$, local additive characters $\psi_v$ of $F_v$, and set-theoretic sections $\mathrm{sec}_v : \mathcal{O}_F/v \to \mathcal{O}_F$ of the quotient maps, such that for all $v \notin S$: the family indexed by $\mathrm{Option}(\mathcal{O}_F/v)$ whose value at the base point is the image of $w\,\mathrm{diag}(\varpi_v,1)\,w$ and at $c$ the image of $n(\mathrm{sec}_v(c))\,\mathrm{diag}(\varpi_v,1)$ is a Hecke coset system for the subgroup $\mathrm{levelOne}(\mathrm{level}\,\Phi) \cap \ker(\mathrm{glArch})$ and the element $\mathrm{heckeGen}(v)$, that is, its members lie in the double coset, cover it modulo the subgroup, and represent pairwise distinct cosets; the image of $\mathrm{diag}(\varpi_v,1)$ equals $\mathrm{heckeGen}(v)$; $\psi_v$ is trivial on $\mathcal{O}_v$ but nontrivial on $\varpi_v^{-1}\mathcal{O}_v$; and for every $x \in F_v$, every $g \in \mathrm{GL}_2(\mathbb{A}_F)$ and every function $W$ on $\mathrm{GL}_2(\mathbb{A}_F)$ invariant under left translation by unipotents with rational entry, the Whittaker coefficient of $W$ at $\alpha = 1$ with respect to $\psi$ and these pins satisfies $W^{(1)}(\iota_v(n(x))\,g) = \psi_v(x)\,W^{(1)}(g)$.
--
--   This is the standard book-keeping step that fixes a single finite set of finite places outside which all the data attached to an automorphic form — its level, its exceptional Hecke places, the ramification of the twisting idele character, and the conductor of the additive character — are simultaneously unramified, and which in addition records one consistent choice of local uniformisers, local additive components, residue sections and local Hecke coset representatives. It is used in the derivation of the Euler product for the twisted $L$-function of an arithmetic genuine cusp realisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_SmoothCuspRealizationAt_exists_finset_badSet_rightConv_section.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_SmoothCuspRealization
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_AutomorphicForm_ArithCuspRealization
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_UnramifiedWhittaker_ZetaIntegrand
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix MeasureTheory
open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdeleRing NumberField.TateGlobal NumberField.AdelicBox
open AutomorphicForm AdelicDock UnramifiedWhittaker

theorem AutomorphicForm.SmoothCuspRealizationAt.exists_finset_badSet_rightConv_section
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (Φ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F
        (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
          (adelicBox F)) Φ.toRawCentral)
    (φ f : AdelicGL2 (𝓞 F) F → ℂ) (hR : R.toFun = rightConv F φ f)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ)
    (S₀ : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S ∧ R.exceptionalSet ⊆ S ∧
      (∀ v ∉ S, ¬ v.asIdeal ∣ Φ.level) ∧
      (∀ v ∉ S, IsUnramifiedCharAt χ v) ∧
      (∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      χ u = 1) ∧
      (∀ u : (AdeleRing (𝓞 F) F)ˣ,
      (u : AdeleRing (𝓞 F) F).1 = 1 →
      (∀ v ∈ S, (u : AdeleRing (𝓞 F) F).2 v = 1) →
      finitePartUnits (𝓞 F) F u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F →
      ideleNorm F u = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F),
      ideleNorm F (uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹) ∧
      (∀ v ∉ S, ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers F)) (g : AdelicGL2 (𝓞 F) F),
          rightConv F φ f (g * placeEmbed F v
            (Matrix.GeneralLinearGroup.map
              (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) kv)) = rightConv F φ f g) ∧
      ∃ (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
        (hπ : ∀ v : HeightOneSpectrum (𝓞 F),
          algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v) ≠ 0)
        (ψv : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ)
        (sec : ∀ v : HeightOneSpectrum (𝓞 F), 𝓞 F ⧸ v.asIdeal → 𝓞 F),
        (∀ (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F ⧸ v.asIdeal), Ideal.Quotient.mk v.asIdeal (sec v c) = c) ∧
        (∀ v ∉ S,
          HeckeIntegralSeam.IsHeckeCosetSystem
            (levelOne (𝓞 F) F Φ.level ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v)
            (fun i : Option (𝓞 F ⧸ v.asIdeal) =>
              finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
                (i.elim (LocalGL2.localRepInf (ϖ v) (hπ v))
                  (fun c => LocalGL2.localRepSome (ϖ v) (hπ v)
                    (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec v c))))))) ∧
        (∀ v ∉ S, finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (LocalGL2.diagPi (ϖ v) (hπ v))) = heckeGen (𝓞 F) F v) ∧
        (∀ v ∉ S, ∀ r : v.adicCompletionIntegers F,
      ψv v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) = 1) ∧
        (∀ v ∉ S, ∃ r : v.adicCompletionIntegers F,
      ψv v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r /
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) ≠ 1) ∧
        (∀ v ∉ S, ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) (W : AdelicGL2 (𝓞 F) F → ℂ),
            (∀ (β : F) (h : AdelicGL2 (𝓞 F) F),
              W (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * h) = W h) →
            whittakerCoefficient F
              (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
                (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ W 1 (placeEmbed F v (unipotent x) * g) =
            ψv v x * whittakerCoefficient F
              (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
                (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ψ W 1 g) := by sorry
