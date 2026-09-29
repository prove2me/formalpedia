-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_isCoarseModuli_pullback_fst_eq_of_injective_of_isUnit_of_isUnit_two_of_isUnit_three
-- name    : CerednikDrinfeld.QM.IsCoarseModuli.exists_isCoarseModuli_pullback_fst_eq_of_injective_of_isUnit_of_isUnit_two_of_isUnit_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:14.319112+00:00
-- url     : https://prove2.me/theorems/3798af09-1711-5e75-94ee-3ac08110388f
-- title:
--   Base change of coarse moduli of fake elliptic curves to a field
-- statement:
--   Fix distinct primes $q' \neq q$ and rationals $a,b$ such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every height-one place $v$ of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra precisely when $v$ contains $q$ or $q'$. Let $\Lambda\subseteq\mathbb{H}[\mathbb{Q},a,b]$ be a $\mathbb{Z}$-submodule which is an order maximal among orders, let $N\neq 0$, let $\mathcal{O}$ be a domain of characteristic zero in which $N$, $2$ and $3$ are units, and let $m_0\geq 3$ be a natural number which is a unit in $\mathcal{O}$. Let $\pi_X : X \to \operatorname{Spec}\mathcal{O}$ be a morphism of schemes together with a rule $\mathrm{pt}$ assigning to every commutative ring $S$, every $s : \operatorname{Spec} S \to \operatorname{Spec}\mathcal{O}$ and every fake elliptic curve $E$ over $S$ with $\Lambda$-action and level-$N$ data (an abelian scheme of fibre dimension $2$ with commutative relative group law, a $\Lambda$-action satisfying the trace condition, and the level structures of `FakeEllipticCurve`) a morphism $\operatorname{Spec} S \to X$ over $\pi_X$, and assume $(X,\pi_X,\mathrm{pt})$ is a coarse moduli datum in the sense of `IsCoarseModuli`: $\mathrm{pt}$ is constant on isomorphism classes, compatible with base change along ring homomorphisms and pullback of curves, surjective and injective up to isomorphism on points valued in algebraically closed fields, and universal among such rules. Assume further that $\pi_X$ is separated and locally of finite type. Then for every field $k$ and every injective ring homomorphism $i : \mathcal{O}\to k$ there is a rule $\mathrm{pt}_k$, defined on $k$-bases and valued in morphisms over the second projection of the fibre product $X\times_{\operatorname{Spec}\mathcal{O}}\operatorname{Spec} k$, such that this projection together with $\mathrm{pt}_k$ is again a coarse moduli datum for fake elliptic curves with $\Lambda$ and $N$, and such that for all $S$, all $s : \operatorname{Spec} S \to \operatorname{Spec} k$ and all $E$, the morphism $\mathrm{pt}_k(S,s,E)$ followed by the first projection equals $\mathrm{pt}(S, s \text{ followed by } \operatorname{Spec}(i), E)$.
--
--   This is the base-change stability of the coarse moduli scheme of fake elliptic curves with $\Lambda$-action and level-$N$ structure along an injection of the base domain into a field, with the extra assertion that the new point rule is compatible with the old one via the projection to $X$. It is used by the corresponding existence statement without the compatibility clause, and in the comparison of moduli towers with their completions in the Čerednik–Drinfeld uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_IsCoarseModuli_exists_isCoarseModuli_pullback_fst_eq_of_injective_of_isUnit_of_isUnit_two_of_isUnit_three.lean

import Definitions.Def_CerednikDrinfeld_QMCoarseModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open CategoryTheory AlgebraicGeometry QuaternionAlgebra CerednikDrinfeld NeronModelInfra
open CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.IsCoarseModuli.exists_isCoarseModuli_pullback_fst_eq_of_injective_of_isUnit_of_isUnit_two_of_isUnit_three
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q) {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (N : ℕ) [NeZero N]
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [CharZero 𝒪] (hN : IsUnit ((N : ℕ) : 𝒪))
    (h2 : IsUnit ((2 : ℕ) : 𝒪)) (h3 : IsUnit ((3 : ℕ) : 𝒪))
    (m₀ : ℕ) (hm₀ : 3 ≤ m₀) (hm₀u : IsUnit ((m₀ : ℕ) : 𝒪))
    {X : Scheme.{0}} {πX : X ⟶ Spec (CommRingCat.of 𝒪)}
    {pt : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of 𝒪)), FakeEllipticCurve Λ N S → SchemeHomOver s πX}
    (hX : IsCoarseModuli Λ N X πX pt) (hsep : IsSeparated πX) (hlft : LocallyOfFiniteType πX)
    (k : Type) [Field k] (i : 𝒪 →+* k) (hi : Function.Injective i) :
    ∃ ptk : ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of k)),
        FakeEllipticCurve Λ N S → SchemeHomOver s (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom i))),
      IsCoarseModuli Λ N (Limits.pullback πX (Spec.map (CommRingCat.ofHom i)))
        (Limits.pullback.snd πX (Spec.map (CommRingCat.ofHom i))) ptk ∧
      ∀ (S : Type) [CommRing S] (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of k)) (E : FakeEllipticCurve Λ N S),
        (ptk S s E).1 ≫ Limits.pullback.fst πX (Spec.map (CommRingCat.ofHom i)) =
          (pt S (s ≫ Spec.map (CommRingCat.ofHom i)) E).1 := by sorry
