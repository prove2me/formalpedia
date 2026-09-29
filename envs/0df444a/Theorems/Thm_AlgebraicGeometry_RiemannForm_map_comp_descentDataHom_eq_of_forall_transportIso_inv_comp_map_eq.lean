-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq
-- name    : AlgebraicGeometry.RiemannForm.map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/2a43b9d2-0232-5888-bdd8-72335b013cfe
-- title:
--   Translation-invariance makes e₀ a morphism of descent data
-- statement:
--   Let $k$ be an algebraically closed field, $A$ a scheme with a morphism $f : A \to \operatorname{Spec} k$, and $L$ a relative group law on $f$ (a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of sections over varying $t : T \to \operatorname{Spec} k$, natural in $T$), assumed commutative by `hc`; let `hA` record that $f$ is smooth and proper with connected fibres and admits a relative group law. Let $\mathcal M, \mathcal M'$ be $\mathcal O_A$-modules, let $g \in \mathbb N$ be such that every fibre $f^{-1}(s)$ has topological Krull dimension $g$, and let $n \in \mathbb N$ with $n \neq 0$ in $k$; write $[n] =$ `L.schemeNsmul n` $: A \to A$ for the endomorphism obtained by $n$-fold $L$-multiplication of the identity section with itself. Let $e_0 : [n]^{*}\mathcal M \to [n]^{*}\mathcal M'$ be a morphism of $\mathcal O_A$-modules, where pullback is taken through the pseudofunctor $X \mapsto \mathcal O_X\text{-Mod}$. Assume (`HSQ`) that $e_0$ is invariant under transport along translations by $n$-torsion $k$-points: for every $P$ in the additive group of sections of $f$ over $\operatorname{Spec} k$ with $n \cdot P = 0$, writing $T_P$ for the translation $L$-multiplication by the constant point $P$ and given any proof $hx$ that $T_P$ followed by $[n]$ equals $[n]$, the inverse of the transport isomorphism `transportIso hx 𝓜` $: T_P^{*}[n]^{*}\mathcal M \cong [n]^{*}\mathcal M$ followed by $T_P^{*}e_0$ equals $e_0$ followed by the inverse of `transportIso hx 𝓜'`. Then for every scheme $Y$, every $q : Y \to A$, and all $f_1, f_2 : Y \to A$ (indexed by the one-element family constant at $[n]$, with indices $i_1, i_2 : \mathrm{Unit}$) satisfying $f_1$ followed by $[n]$ equals $q$ and $f_2$ followed by $[n]$ equals $q$, one has that $f_1^{*}e_0$ followed by the transition morphism at $(q; f_1, f_2)$ of the canonical descent datum `toDescentData` on $\mathcal M'$ equals the corresponding transition morphism for $\mathcal M$ followed by $f_2^{*}e_0$.
--
--   This is the cocycle, or descent-datum, compatibility: it says that a translation-invariant morphism $e_0$ between the $[n]$-pullbacks of two $\mathcal O_A$-modules is a morphism of the canonical descent data along the single covering morphism $[n] : A \to A$. It is used in the construction of the descended isomorphism in [`AlgebraicGeometry.RiemannForm.exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq`](thm.html#AlgebraicGeometry.RiemannForm.exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq), and rests on the covering of $Y$ by opens on which $f_2$ agrees with $f_1$ followed by a translation by an $n$-torsion point.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RiemannForm
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.RiemannForm

theorem AlgebraicGeometry.RiemannForm.map_comp_descentDataHom_eq_of_forall_transportIso_inv_comp_map_eq
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 𝓜' : A.Modules)
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (e₀ : (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (L.schemeNsmul n).op.toLoc).toFunctor.obj 𝓜 ⟶ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (L.schemeNsmul n).op.toLoc).toFunctor.obj 𝓜')
    (HSQ : ∀ (P : L.AlgPoints hc k), n • P = 0 →
      ∀ (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n),
        (transportIso hx 𝓜).inv ≫ (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map (translation f L (RelativeGroupLaw.AlgPoints.toPoint P)).op.toLoc).toFunctor.map e₀ =
          e₀ ≫ (transportIso hx 𝓜').inv)
    ⦃Y : Scheme.{0}⦄ (q : Y ⟶ A) ⦃i₁ i₂ : Unit⦄ (f₁ f₂ : Y ⟶ A)
    (hf₁ : f₁ ≫ (fun _ : Unit => L.schemeNsmul n) i₁ = q) (hf₂ : f₂ ≫ (fun _ : Unit => L.schemeNsmul n) i₂ = q) :
    (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₁.op.toLoc).toFunctor.map e₀ ≫
        ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => L.schemeNsmul n)).obj 𝓜').hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ =
      ((((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).toDescentData (fun _ : Unit => L.schemeNsmul n)).obj 𝓜).hom q (i₁ := i₁) (i₂ := i₂) f₁ f₂ hf₁ hf₂ ≫
        (((Scheme.Modules.pseudofunctor.{0}).comp Bicategory.Adj.forget₁).map f₂.op.toLoc).toFunctor.map e₀ := by sorry
