-- Prove2me | Theorems.Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_represents_of_representsLatticeActions_of_isUnit_two
-- name    : AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_represents_of_representsLatticeActions_of_isUnit_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/fd0c4bee-0267-5c41-b4a9-d79f785f32a7
-- title:
--   Representability of QM structures on polarised abelian surfaces
-- statement:
--   Fix distinct primes $q' \neq q$ and $a,b \in \mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, every nonzero element of $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit exactly when $v$ contains $q$ or $q'$. Let $\Lambda \subseteq \mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $\mu \in \Lambda$ satisfy $\mu^{2} = -(qq')\cdot 1$, let $\mathrm{star} : \Lambda \to \Lambda$ satisfy $\mu\,\mathrm{star}(x) = \bar{x}\mu$ for all $x \in \Lambda$, and let $\beta : \mathrm{Fin}\,4 \to \Lambda$ be such that each $x \in \Lambda$ is uniquely $\sum_j c_j\beta_j$ with $c_j \in \mathbb{Z}$. Let $d,m$ be naturals with $m \geq 3$, let $R$ be a commutative ring in which $m$ and $2$ are units, and let $X$ be a polarised abelian scheme over $R$ of relative fibre dimension $2$, with $2\cdot 2$ level-$m$ points forming a basis of the $m$-torsion on geometric fibres and an invertible, very ample polarisation module of geometric fibre $H^0$-rank $d$. Let $\pi_E : E \to \operatorname{Spec} R$ and a rule $\mathrm{cl}$, assigning to each $\varphi : R \to R'$, each group-law pullback $g$ of $X.L$ along $\varphi$ and each $\Lambda$-action on it a point of $\pi_E$ over $\operatorname{Spec} R'$, satisfy `RepresentsLatticeActions`: $\mathrm{cl}$ is compatible with further base change and is bijective onto the points of $\pi_E$ for each fixed pullback. Assume $\pi_E$ is separated, locally of finite type and locally of finite presentation, and that for every $e : \mathrm{Fin}\,4 \to \mathbb{N}$ there is an open $U \subseteq E$ whose underlying set is closed, with $U \hookrightarrow E$ followed by $\pi_E$ quasi-compact, such that the set-theoretic image of $\mathrm{cl}(\varphi, L', g, X')$ lies in $U$ if and only if for all $j$ and all geometric points of $\operatorname{Spec} R'$ the geometric fibre $H^0$-rank of $g^{*}X.\mathrm{pol} \otimes X'.\mathrm{act}(\beta_j)^{*}g^{*}X.\mathrm{pol}$ equals $e_j$. The conclusion asserts the existence of a scheme $Z$, a morphism $\zeta : Z \to \operatorname{Spec} R$, and a rule $\mathrm{ptZ}$ attaching to every commutative ring $T$, ring map $\varphi : R \to T$, polarised abelian scheme $X'$ over $T$ of the same invariants, witness that $X'$ is the pullback of $X$ along $\varphi$ (in the sense of `PolarisedAbelianScheme.IsPullback`), and `QMStructure` for $(\Lambda,\mathrm{star},\beta)$ on $X'$, a morphism $\operatorname{Spec} T \to Z$ composing with $\zeta$ to $\operatorname{Spec}\varphi$, such that: $\zeta$ is separated, quasi-compact and locally of finite presentation; $\mathrm{ptZ}$ is natural, in that for $\psi : T \to T'$ with $\psi \circ \varphi = \varphi'$ and QM structures $s'$, $s''$ over $T$, $T'$ with `QMStructure.IsPullback` $\psi\, s'\, s''$, the point of $s''$ equals $\operatorname{Spec}\psi$ followed by the point of $s'$; and for each fixed $T$, $\varphi$, $X'$ and pullback witness, $\mathrm{ptZ}$ is surjective onto the $T$-points of $\zeta$ over $\operatorname{Spec}\varphi$ and injective on QM structures.
--
--   This is the representability step for quaternionic multiplication structures: from a scheme representing $\Lambda$-actions on the base changes of a polarised abelian surface with full level-$m$ structure, one obtains a scheme representing those $\Lambda$-actions that constitute a QM structure (Drinfeld's trace condition, a level generator matched by $\beta$, and a polarisation which is locally the cube of a canonical polarisation datum for $\mathrm{star}$), with $\zeta$ separated, quasi-compact and locally of finite presentation. It feeds the construction of the fine moduli scheme of fake elliptic curves with level structure used in the Čerednik–Drinfeld part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_PolarisedAbelianScheme_QMStructure_exists_represents_of_representsLatticeActions_of_isUnit_two.lean

import Definitions.Def_CerednikDrinfeld_QMStructureOnPolarised
import Definitions.Def_CerednikDrinfeld_QMLatticeAction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry QuaternionAlgebra NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.PolarisedAbelianScheme CerednikDrinfeld CerednikDrinfeld.QM

theorem AlgebraicGeometry.PolarisedAbelianScheme.QMStructure.exists_represents_of_representsLatticeActions_of_isUnit_two
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (μ : ↥Λ) (hμ : (μ : ℍ[ℚ, a, b]) * (μ : ℍ[ℚ, a, b]) = -(((q * q' : ℕ) : ℚ) • (1 : ℍ[ℚ, a, b])))
    (star : ↥Λ → ↥Λ) (hstar : ∀ x : ↥Λ, (μ : ℍ[ℚ, a, b]) * (star x : ℍ[ℚ, a, b]) = Star.star (x : ℍ[ℚ, a, b]) * μ)
    (β : Fin (2 * 2) → ↥Λ) (hβ : ∀ x : ↥Λ, ∃! c : Fin (2 * 2) → ℤ, x = ∑ j, c j • β j)
    (d m : ℕ) (hm : 3 ≤ m)
    (R : Type) [CommRing R] (hm' : IsUnit ((m : ℕ) : R)) (h2 : IsUnit (2 : R)) (X : PolarisedAbelianScheme 2 d m R)
    (E : Scheme.{0}) (πE : E ⟶ Spec (CommRingCat.of R))
    (cl : ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
        (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A), IsGroupPullback φ X.L L' g →
        LatticeAction Λ f' L' → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) πE)
    (hE : RepresentsLatticeActions Λ X.L E πE cl) (hEsep : IsSeparated πE) (hElft : LocallyOfFiniteType πE)
    (hElfp : LocallyOfFinitePresentation πE)
    (hEpieces : (∀ e : Fin (2 * 2) → ℕ, ∃ U : E.Opens, IsClosed (U : Set E) ∧ QuasiCompact (U.ι ≫ πE) ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R') {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of R')}
          (L' : RelativeGroupLaw R' f') (g : A' ⟶ X.A) (hg : IsGroupPullback φ X.L L' g) (X' : LatticeAction Λ f' L'),
          (Set.range (cl R' φ L' g hg X').1.base ⊆ (U : Set E) ↔
            ∀ (j : Fin (2 * 2)) (k : Type) [Field k] [IsAlgClosed k] (sk : R' →+* k),
              Scheme.Modules.geomFibreH0Finrank f'
                ((Scheme.Modules.pullback g).obj X.pol ⊗
                  (Scheme.Modules.pullback (X'.act (β j))).obj ((Scheme.Modules.pullback g).obj X.pol)) k sk = e j))) :
    ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of R))
      (ptZ : ∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T),
        PolarisedAbelianScheme.IsPullback φ X X' → QMStructure Λ star β X' →
          SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
      IsSeparated ζ ∧ QuasiCompact ζ ∧ LocallyOfFinitePresentation ζ ∧

      (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : R →+* T) (φ' : R →+* T') (ψ : T →+* T')
          (hψ : ψ.comp φ = φ')
          (X' : PolarisedAbelianScheme 2 d m T) (X'' : PolarisedAbelianScheme 2 d m T')
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (hX'' : PolarisedAbelianScheme.IsPullback φ' X X'')
          (s' : QMStructure Λ star β X') (s'' : QMStructure Λ star β X''),
        QMStructure.IsPullback ψ s' s'' →
          (ptZ T' φ' X'' hX'' s'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ X' hX' s').1) ∧

      (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),
        ∃ s' : QMStructure Λ star β X', ptZ T φ X' hX' s' = z) ∧

      (∀ (T : Type) [CommRing T] (φ : R →+* T) (X' : PolarisedAbelianScheme 2 d m T)
          (hX' : PolarisedAbelianScheme.IsPullback φ X X') (s' s'' : QMStructure Λ star β X'),
        ptZ T φ X' hX' s' = ptZ T φ X' hX' s'' → s' = s'') := by sorry
