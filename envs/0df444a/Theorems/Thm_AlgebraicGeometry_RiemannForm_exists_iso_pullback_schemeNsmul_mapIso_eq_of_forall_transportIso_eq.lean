-- Prove2me | Theorems.Thm_AlgebraicGeometry_RiemannForm_exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq
-- name    : AlgebraicGeometry.RiemannForm.exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.223894+00:00
-- url     : https://prove2.me/theorems/59a5a5e6-af8e-594a-b0c7-ef4b3ae1cbc4
-- title:
--   Translation-invariant isomorphism along [n] descends
-- statement:
--   Let $k$ be an algebraically closed field, let $f : A \to \operatorname{Spec} k$ be a scheme over $k$, and let $L$ be a relative group law on $f$, i.e. a group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over each $t : T \to \operatorname{Spec} k$, natural in $T$; assume $L$ is commutative ($hc$) and that $f$ satisfies the bundle of properties `AbelianSchemePropertyBundle`: $f$ is smooth, proper, has connected fibres, and admits a relative group law. Let $\mathcal M, \mathcal M'$ be $\mathcal O_A$-modules that are invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the pullback along $U \hookrightarrow A$ is isomorphic to the unit module. Let $g : \mathbb{N}$ be such that every fibre of $f$ has topological Krull dimension $g$, and let $n : \mathbb{N}$ with $n \neq 0$ in $k$; write $[n] :=$ `L.schemeNsmul n` for the endomorphism of $A$ underlying $n \cdot \mathrm{id}$. Given an isomorphism $\beta : [n]^*\mathcal M \cong [n]^*\mathcal M'$ such that for every $k$-point $P$ of the group $L$ with $n \cdot P = 0$ and every witness $hx$ of $T_P \circ [n] = [n]$ (composition of the translation $T_P$ by $P$ with $[n]$), the composite of `(transportIso hx 𝓜).symm`, of $T_P^*\beta$, and of `transportIso hx 𝓜'` equals $\beta$ — where `transportIso` is the canonical isomorphism $T_P^*[n]^*\mathcal N \cong [n]^*\mathcal N$ coming from compatibility of pullbacks with composition together with $hx$ — the conclusion is that there exists an isomorphism $\alpha : \mathcal M \cong \mathcal M'$ with $[n]^*\alpha = \beta$.
--
--   This is the descent step in the construction of the level pairing on $n$-torsion: invariance of $\beta$ under all translations by $n$-torsion points is exactly the descent datum for the multiplication-by-$n$ morphism, so $\beta$ comes from an isomorphism of $\mathcal M$ with $\mathcal M'$ on $A$ itself. It is used in [`AlgebraicGeometry.RiemannForm.forall_isLevelPairingValue_one_iff_nonempty_pullback_translation_iso`](thm.html#AlgebraicGeometry.RiemannForm.forall_isLevelPairingValue_one_iff_nonempty_pullback_translation_iso).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RiemannForm_exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq.lean

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

theorem AlgebraicGeometry.RiemannForm.exists_iso_pullback_schemeNsmul_mapIso_eq_of_forall_transportIso_eq
    (k : Type) [Field k] [IsAlgClosed k] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle k f)
    (𝓜 𝓜' : A.Modules) (h𝓜 : Scheme.Modules.IsInvertible 𝓜) (h𝓜' : Scheme.Modules.IsInvertible 𝓜')
    (g : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of k)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = g)
    (n : ℕ) (hn : (n : k) ≠ 0)
    (β : (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓜 ≅ (Scheme.Modules.pullback (L.schemeNsmul n)).obj 𝓜')
    (hβ : ∀ (P : L.AlgPoints hc k), n • P = 0 →
      ∀ (hx : translation f L (RelativeGroupLaw.AlgPoints.toPoint P) ≫ L.schemeNsmul n = L.schemeNsmul n),
        (transportIso hx 𝓜).symm ≪≫
          (Scheme.Modules.pullback (translation f L (RelativeGroupLaw.AlgPoints.toPoint P))).mapIso β ≪≫
            transportIso hx 𝓜' = β) :
    ∃ α : 𝓜 ≅ 𝓜', (Scheme.Modules.pullback (L.schemeNsmul n)).mapIso α = β := by sorry
