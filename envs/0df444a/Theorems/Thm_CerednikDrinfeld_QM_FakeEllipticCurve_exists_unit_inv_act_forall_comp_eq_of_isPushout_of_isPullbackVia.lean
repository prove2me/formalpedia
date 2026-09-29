-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/5d868857-841f-5798-820d-93e4241a7845
-- title:
--   Gluing unit, inversion and Λ-action over a pushout
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$, and $N\in\mathbb{N}$. Let $B,B',B''$ be commutative rings and $\varphi':B'\to B$, $\varphi'':B''\to B$ surjective ring homomorphisms whose kernels are nilpotent ideals. Let $E'$, $E''$, $E_B$ be fake elliptic curves of level data $(\Lambda,N)$ over $B'$, $B''$, $B$ respectively, and let $h':E_B.A\to E'.A$, $h'':E_B.A\to E''.A$ exhibit $E_B$ as the base change of $E'$ along $\varphi'$ and of $E''$ along $\varphi''$ in the sense of `IsPullbackVia`: each $h$ makes the square with the structure morphisms and $\operatorname{Spec}$ of the ring map a pullback of schemes, is compatible with the relative group laws on points, commutes with the $\Lambda$-actions, and carries points factoring through the level structure to points factoring through the level structure downstairs. Write $P=\{(x,y)\in B'\times B'' : \varphi'(x)=\varphi''(y)\}$ with its two projections `pullbackFst`, `pullbackSnd`. Let $f:X\to\operatorname{Spec}P$ be a flat morphism of schemes, and $k':E'.A\to X$, $k'':E''.A\to X$ morphisms making each square over $\operatorname{Spec}P$ with $\operatorname{Spec}$ of the corresponding projection a pullback, with $h'\!\gg\!k'=h''\!\gg\!k''$ and with $(k',k'')$ a pushout of $(h',h'')$. Then there exist a section $e$ of $f$ over $\operatorname{Spec}P$, an endomorphism $\iota$ of $X$ over $f$, and endomorphisms $\mathrm{act}(x)$ of $X$ over $f$ indexed by $x\in\Lambda$, such that for every scheme $T$ and every $t':T\to\operatorname{Spec}B'$ the unit point of $E'$ at $t'$, followed by $k'$, equals $t'$ followed by $\operatorname{Spec}$ of `pullbackFst` followed by $e$; for every $T$-point $Q$ of $E'.A$ over $t'$ the inverse point $(E'.L.\mathrm{inv}\,t'\,Q)$ followed by $k'$ equals $Q$ followed by $k'$ followed by $\iota$; and $E'.\mathrm{act}(x)$ followed by $k'$ equals $k'$ followed by $\mathrm{act}(x)$ for all $x\in\Lambda$; and the three corresponding identities hold for $E''$ along $k''$ with $\operatorname{Spec}$ of `pullbackSnd`.
--
--   This is the gluing step for the non-binary structure morphisms in the deformation theory of fake elliptic curves: $\operatorname{Spec}P$ is the pushout of $\operatorname{Spec}B'\leftarrow\operatorname{Spec}B\to\operatorname{Spec}B''$ for surjections with nilpotent kernel, and the total space $X$ is assumed to be the corresponding pushout of total spaces, so the unit section, the inversion and the $\Lambda$-action of $E'$ and $E''$, agreeing over $E_B$, descend to $X$. It is used by the companion statement which also glues the multiplication of the relative group law.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open IsLocalRing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal CerednikDrinfeld.SpecialFormal.ModuliPackage NeronModelInfra GoodReductionJacobian

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_unit_inv_act_forall_comp_eq_of_isPushout_of_isPullbackVia
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B)
    (hφ's : Function.Surjective φ') (hφ''s : Function.Surjective φ'')
    (hφ'n : IsNilpotent (RingHom.ker φ')) (hφ''n : IsNilpotent (RingHom.ker φ''))
    (E' : FakeEllipticCurve Λ N B') (E'' : FakeEllipticCurve Λ N B'') (EB : FakeEllipticCurve Λ N B)
    (h' : EB.A ⟶ E'.A) (hh' : FakeEllipticCurve.IsPullbackVia φ' E' EB h')
    (h'' : EB.A ⟶ E''.A) (hh'' : FakeEllipticCurve.IsPullbackVia φ'' E'' EB h'')
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of (pullbackRing φ' φ''))) [Flat f]
    (k' : E'.A ⟶ X) (hk' : CategoryTheory.IsPullback k' E'.f f (Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))))
    (k'' : E''.A ⟶ X) (hk'' : CategoryTheory.IsPullback k'' E''.f f (Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))))
    (hcomm : h' ≫ k' = h'' ≫ k'') (hpo : IsPushout h' h'' k' k'') :
    ∃ (e : Spec (CommRingCat.of (pullbackRing φ' φ'')) ⟶ X) (ι : X ⟶ X) (act : ↥Λ → (X ⟶ X))
      (he : e ≫ f = 𝟙 _) (hι : ι ≫ f = f) (act_over : ∀ x : ↥Λ, act x ≫ f = f),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')),
        (E'.L.one t').1 ≫ k' = (t' ≫ Spec.map (CommRingCat.ofHom (pullbackFst φ' φ''))) ≫ e) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B')) (P : SchemeHomOver t' E'.f),
        (E'.L.inv t' P).1 ≫ k' = (P.1 ≫ k') ≫ ι) ∧
      (∀ x : ↥Λ, E'.act x ≫ k' = k' ≫ act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')),
        (E''.L.one t').1 ≫ k'' = (t' ≫ Spec.map (CommRingCat.ofHom (pullbackSnd φ' φ''))) ≫ e) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B'')) (P : SchemeHomOver t' E''.f),
        (E''.L.inv t' P).1 ≫ k'' = (P.1 ≫ k'') ≫ ι) ∧
      (∀ x : ↥Λ, E''.act x ≫ k'' = k'' ≫ act x) := by sorry
