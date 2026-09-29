-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotientVia_isIsogenyPair_comp_eq_of_comp_eq_act_of_not_isIsogenyPair
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotientVia_isIsogenyPair_comp_eq_of_comp_eq_act_of_not_isIsogenyPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:06.112671+00:00
-- url     : https://prove2.me/theorems/095e4fa0-ec43-5d79-a530-b842bcefeacf
-- title:
--   Factoring a norm r^ē r endomorphism through the Atkin–Lehner quotient
-- statement:
--   Fix primes $r$ and $\bar r$ with $\bar r \neq r$, and a nonzero level $N$ with $\bar r \nmid N$. Let $a, b \in \mathbb{Q}$ be such that $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b r rbar`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all nonzero elements invertible exactly when $v$ contains $r$ or $\bar r$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is an order maximal among orders under inclusion and contains every rational integer, let $k_0$ be an algebraically closed field of characteristic $r$, let $A_0$ be a fake elliptic curve over $k_0$ for $\Lambda$ and level $N$ (a two-dimensional abelian scheme-like object with commutative relative group law, $\Lambda$-action `act` and level map `lev`), and let $e \in \mathbb{N}$. Let $f, f' : A_0.A \to A_0.A$ be morphisms over $k_0$ which are homomorphisms for the relative group law on $T$-points, commute with the action of every $m \in \Lambda$, satisfy $f \circ f' = f' \circ f = \mathrm{act}(r^e \bar r)$, and such that $f$ preserves the level structure (a $T$-point factoring through `A₀.lev` is carried to one factoring through `A₀.lev`); assume moreover that for no $j \in \mathbb{N}$ and no $\psi$ is $(f,\psi)$, or $(f',\psi)$, an isogeny pair of degree $r^j$ from $A_0$ to $A_0$ in the sense of `IsIsogenyPair`. The conclusion asserts the existence of a fake elliptic curve $A_{0,w}$ over $k_0$ for $\Lambda$ and level $N$, morphisms $a_w : A_0.A \to A_{0,w}.A$ and $a_w' : A_{0,w}.A \to A_0.A$ over $k_0$, a natural number $k_w$, and morphisms $b_w : A_{0,w}.A \to A_0.A$ (over $k_0$) and $b_w' : A_0.A \to A_{0,w}.A$ such that: $(a_w, a_w')$ exhibits $A_{0,w}$ as the Atkin–Lehner quotient at $\bar r$, namely both are group-law homomorphisms on points, both are $\Lambda$-equivariant, both composites equal the action of $\bar r$ whenever $\bar r \in \Lambda$, a $T$-point $P$ of $A_0$ is killed by $a_w$ precisely when it is killed by $\mathrm{act}(m)$ for every $m \in \Lambda$ with $m\,\overline{m} = \bar r n$ for some $n \in \mathbb{Z}$, and $a_w$ preserves the level structure; $(b_w, b_w')$ is an isogeny pair of degree $r^{k_w}$ from $A_{0,w}$ to $A_0$; $b_w$ preserves the level structure; and $a_w$ followed by $b_w$ equals $f$.
--
--   This is the factorisation step in the Čerednik–Drinfel'd analysis of endomorphisms of fake elliptic curves in characteristic $r$: an endomorphism whose norm is $r^e\bar r$ and which is not, up to $r$-power isogeny, already an endomorphism of $A_0$ must factor as the degree-$\bar r$ Atkin–Lehner quotient map followed by an $r$-power isogeny back to $A_0$. It is used in the construction of the Atkin–Lehner dictionary on the special fibre, via `exists_atkinLehnerDictionary_of_endomorphismDictionary_endIsoFull`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_exists_isAtkinLehnerQuotientVia_isIsogenyPair_comp_eq_of_comp_eq_act_of_not_isIsogenyPair.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification
import Definitions.Def_CerednikDrinfeld_QMIsogeny
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra IsDedekindDomain CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion TensorProduct NumberField

theorem CerednikDrinfeld.QM.FakeEllipticCurve.exists_isAtkinLehnerQuotientVia_isIsogenyPair_comp_eq_of_comp_eq_act_of_not_isIsogenyPair
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N] (hrr : rbar ≠ r) (hrbarN : ¬ rbar ∣ N)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b r rbar)
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hΛℤ : ∀ m : ℤ, ((m : ℚ) : ℍ[ℚ, a, b]) ∈ Λ)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] [CharP k₀ r] (A₀ : FakeEllipticCurve Λ N k₀) (e : ℕ)
    (f f' : A₀.A ⟶ A₀.A) (hf : f ≫ A₀.f = A₀.f) (hf' : f' ≫ A₀.f = A₀.f)
    (hf_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f hf (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f hf P) (mapPt f hf Q))
    (hf'_hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k₀)) (P Q : SchemeHomOver t A₀.f),
      mapPt f' hf' (A₀.L.mul t P Q) = A₀.L.mul t (mapPt f' hf' P) (mapPt f' hf' Q))
    (hf_lin : ∀ m : ↥Λ, A₀.act m ≫ f = f ≫ A₀.act m) (hf'_lin : ∀ m : ↥Λ, A₀.act m ≫ f' = f' ≫ A₀.act m)
    (hf_lev : FakeEllipticCurve.PreservesLevel A₀ A₀ f hf)
    (hff' : f ≫ f' = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩) (hf'f : f' ≫ f = A₀.act ⟨(((r ^ e * rbar : ℕ) : ℤ) : ℚ), hΛℤ _⟩)
    (hf_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f ψ)
    (hf'_not : ∀ (j : ℕ) (ψ : A₀.A ⟶ A₀.A), ¬ FakeEllipticCurve.IsIsogenyPair (r ^ j) A₀ A₀ f' ψ) :
    ∃ (A₀w : FakeEllipticCurve Λ N k₀)
      (aw : A₀.A ⟶ A₀w.A) (haw : aw ≫ A₀w.f = A₀.f) (aw' : A₀w.A ⟶ A₀.A) (haw' : aw' ≫ A₀.f = A₀w.f)
      (kw : ℕ) (bw : A₀w.A ⟶ A₀.A) (hbw : bw ≫ A₀.f = A₀w.f) (bw' : A₀.A ⟶ A₀w.A),
      FakeEllipticCurve.IsAtkinLehnerQuotientVia rbar A₀ A₀w aw haw aw' haw' ∧
      FakeEllipticCurve.IsIsogenyPair (r ^ kw) A₀w A₀ bw bw' ∧ FakeEllipticCurve.PreservesLevel A₀w A₀ bw hbw ∧
      aw ≫ bw = f := by sorry
