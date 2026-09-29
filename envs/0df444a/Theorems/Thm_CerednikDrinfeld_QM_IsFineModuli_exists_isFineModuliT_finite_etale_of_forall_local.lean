-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuliT_finite_etale_of_forall_local
-- name    : CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuliT_finite_etale_of_forall_local
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/4e22daa3-2e21-515f-90d4-bd9d1f54921e
-- title:
--   Gluing a finite étale level-N cover of a fine moduli scheme
-- statement:
--   Let $q \ne q'$ be primes and $a,b \in \mathbb{Q}$ such that $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite ($0<a$ or $0<b$) and, for each height-one prime $v$ of $\mathbb{Q}$, its completion at $v$ is a division algebra exactly when $v$ contains $q$ or $q'$; let $\Lambda \subset \mathbb{H}[\mathbb{Q},a,b]$ be a maximal order (an order — containing $1$, multiplicatively closed, $\mathbb{Q}$-spanning, finitely generated — maximal among orders). Let $N_0$, $N \ne 0$ and $m \ge 3$ be naturals and $\mathcal{O}$ a commutative ring in which the images of $N_0$, $N$ and $m$ are units. Let $\pi_M : M \to \operatorname{Spec}\mathcal{O}$ be a scheme over $\mathcal{O}$ together with a rule $\mathrm{ptF}$ assigning to every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and every pair $u = (E,P)$ of a fake elliptic curve $E$ of level $N_0$ over $S$ and a full level-$m$ structure $P$ on $E$ a morphism $\operatorname{Spec} S \to M$ over $s$, and assume `IsFineModuli`: $\mathrm{ptF}$ is invariant under isomorphism of such pairs, compatible with base change along ring maps, surjective onto the $S$-points of $M$ over $s$, and injective up to isomorphism. Assume furthermore the local hypothesis: for every commutative ring $S$ in which $N_0$, $N$, $m$ are units and every pair $u$ over $S$ there are a scheme $Z$ and a finite étale $\zeta : Z \to \operatorname{Spec} S$ together with a rule $\mathrm{ptZ}$ attaching to each ring map $\varphi : S \to T$, each pair $u'$ over $T$ that is a pullback of $u$ along $\varphi$ and each extra level structure $K$ of order $N$ on $u'$ a point $\operatorname{Spec} T \to Z$ over $\operatorname{Spec}\varphi$, such that $\mathrm{ptZ}$ depends only on which points of $u'$ factor through $K$, is compatible with a further base change $\psi : T \to T'$ realised by a morphism $g$ of the underlying curves that is a pullback via $\psi$, respects the full level sections and carries the extra level $K''$ over $T'$ into $K'$, is surjective onto the points of $\zeta$ over $\operatorname{Spec}\varphi$, and is injective in the sense that equal values force the same factorisation property. Then there exist a scheme $M^{\times}$, a morphism $f : M^{\times} \to M$ and a rule $\mathrm{ptF}^{\times}$ assigning to each $S$, each $s$, each pair $u$ over $S$ and each extra level structure $C$ of order $N$ on $u$ a morphism $\operatorname{Spec} S \to M^{\times}$ over $s$, such that `IsFineModuliT` holds for $\Lambda$, $N_0$, $m$, $N$, $M^{\times}$, $f$ followed by $\pi_M$ and $\mathrm{ptF}^{\times}$, the morphism $f$ is finite and étale, and $\mathrm{ptF}^{\times}(S,s,u,C)$ followed by $f$ equals $\mathrm{ptF}(S,s,u)$.
--
--   This is the globalisation step in the construction of the fine moduli scheme of triples (fake elliptic curve, full level-$m$ structure, extra level structure of order $N$): the relatively representable finite étale local solutions provided by the hypothesis are glued over a fine moduli scheme of pairs, and the forgetful morphism to that scheme is recorded as finite étale and compatible with the two moduli interpretations. It is used by [`CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuliT_finite_etale_forget`](thm.html#CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuliT_finite_etale_forget).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsFineModuli_exists_isFineModuliT_finite_etale_of_forall_local.lean

import Definitions.Def_CerednikDrinfeld_QMFineModuli
import Definitions.Def_CerednikDrinfeld_QMFineModuliT
import Definitions.Def_CerednikDrinfeld_QMCoarseModuli
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM NeronModelInfra

theorem CerednikDrinfeld.QM.IsFineModuli.exists_isFineModuliT_finite_etale_of_forall_local
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N₀ : ℕ) (N : ℕ) [NeZero N] (m : ℕ) (hm : 3 ≤ m)
    (𝒪 : Type) [CommRing 𝒪] (hN₀ : IsUnit ((N₀ : ℕ) : 𝒪)) (hN : IsUnit ((N : ℕ) : 𝒪)) (hm' : IsUnit ((m : ℕ) : 𝒪))
    {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of 𝒪)}
    {ptF : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)),
      FakeEllipticCurve.WithFullLevel Λ N₀ m S → SchemeHomOver s πM}
    (hM : IsFineModuli Λ N₀ m M πM ptF)
    (hloc : ∀ (S : Type) [CommRing S], IsUnit ((N₀ : ℕ) : S) → IsUnit ((N : ℕ) : S) → IsUnit ((m : ℕ) : S) →
      ∀ u : FakeEllipticCurve.WithFullLevel Λ N₀ m S,
      ∃ (Z : Scheme.{0}) (ζ : Z ⟶ Spec (CommRingCat.of S)) (_ : IsFinite ζ) (_ : Etale ζ)
        (ptZ : ∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T),
          FakeEllipticCurve.WithFullLevel.IsPullback φ u u' → u'.1.ExtraLevel N → SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ),

        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u') (K K' : u'.1.ExtraLevel N),
            (∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P) → ptZ T φ u' hu' K = ptZ T φ u' hu' K') ∧

        (∀ (T T' : Type) [CommRing T] [CommRing T'] (φ : S →+* T) (ψ : T →+* T')
            (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T) (u'' : FakeEllipticCurve.WithFullLevel Λ N₀ m T')
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (hu'' : FakeEllipticCurve.WithFullLevel.IsPullback (ψ.comp φ) u u'')
            (K' : u'.1.ExtraLevel N) (K'' : u''.1.ExtraLevel N) (g : u''.1.A ⟶ u'.1.A),

            FakeEllipticCurve.IsPullbackVia ψ u'.1 u''.1 g →
            (u''.2.P).1 ≫ g = Spec.map (CommRingCat.ofHom ψ) ≫ (u'.2.P).1 →
            (∀ {T₀ : Scheme.{0}} (t : T₀ ⟶ Spec (CommRingCat.of T')) (P : SchemeHomOver t u''.1.f),
              FactorsThrough K''.levK P → ∃ P₀ : T₀ ⟶ K'.K, P₀ ≫ K'.levK = P.1 ≫ g) →
              (ptZ T' (ψ.comp φ) u'' hu'' K'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (ptZ T φ u' hu' K').1) ∧

        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (z : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ), ∃ K : u'.1.ExtraLevel N, ptZ T φ u' hu' K = z) ∧
        (∀ (T : Type) [CommRing T] (φ : S →+* T) (u' : FakeEllipticCurve.WithFullLevel Λ N₀ m T)
            (hu' : FakeEllipticCurve.WithFullLevel.IsPullback φ u u')
            (K K' : u'.1.ExtraLevel N), ptZ T φ u' hu' K = ptZ T φ u' hu' K' →
            ∀ {T' : Scheme.{0}} (t : T' ⟶ Spec (CommRingCat.of T)) (P : SchemeHomOver t u'.1.f),
              FactorsThrough K.levK P ↔ FactorsThrough K'.levK P)) :
    ∃ (Mx : Scheme.{0}) (f : Mx ⟶ M)
      (ptFx : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N₀ m S),
        u.1.ExtraLevel N → SchemeHomOver s (f ≫ πM)),
      IsFineModuliT Λ N₀ m N Mx (f ≫ πM) ptFx ∧ IsFinite f ∧ Etale f ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)) (u : FakeEllipticCurve.WithFullLevel Λ N₀ m S)
        (C : u.1.ExtraLevel N), (ptFx S s u C).1 ≫ f = (ptF S s u).1 := by sorry
