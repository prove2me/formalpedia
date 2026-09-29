-- Prove2me | Theorems.Thm_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_evalAt_eq
-- name    : AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_evalAt_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/8642b8af-7fab-509b-adbe-5f1db392ab65
-- title:
--   Admissible values of a node coordinate are attained
-- statement:
--   Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, and $F$ a field extension of $L$ that is a curve over $L$ (principal divisors of degree zero, finite residue extensions, $\Omega[F/L]$ free of rank one) and essentially of finite type over $L$. Let $R_1, R_2$ be regular prolongations of $A$ to $F$ with residue fields $\bar F_1, \bar F_2$ over the residue field of $A$: valuation subrings of $F$ meeting $L$ exactly in $A$, with surjective residue maps whose kernels are the maximal ideals, compatible with the residue map of $A$, and such that every nonzero element of $F$ has an $L$-multiple lying in the ring with nonzero residue; let $x_1, x_2$ be places of $\bar F_1, \bar F_2$ over the residue field of $A$, both rational. Let $S$ be a set of places of $F$ over $L$, all rational, and $\mathcal N \subseteq F$ the subring consisting of the $f$ lying in $R_1$, in $R_2$ and in the valuation ring of every $P \in S$; assume the values $P.\mathrm{evalAt}\, f$ for $f \in \mathcal N$, $P \in S$ lie in $A$; that for $f \in \mathcal N$ the nonzero residues of $f$ in $\bar F_1, \bar F_2$ have nonnegative order at $x_1$, resp. $x_2$; and that whenever both residues are nonzero the set of $P \in S$ with $\mathrm{ord}_P f \ne 0$ is finite with $\sum_{P \in S} \mathrm{ord}_P f = \mathrm{ord}_{x_1}(\bar f^{(1)}) + \mathrm{ord}_{x_2}(\bar f^{(2)})$. Let $\mathcal N_0 \le \mathcal N$ be a Noetherian local subring such that $S$ is exactly the set of places $P$ whose valuation ring contains $\mathcal N_0$ and at which every non-unit of $\mathcal N_0$ takes a value in the maximal ideal of $A$, and such that every $f \in F$ satisfies $f b = \sum_{i<n} c_i a_i$ with $0 \ne b \in \mathcal N_0$, $a_i \in \mathcal N_0$, $c_i \in L$. Let $C \subseteq A$ be a subring mapping into $\mathcal N_0$, which is a discrete valuation domain with an element $\varpi \ne 0$ such that $d \in C$ has residue $0$ in the residue field of $A$ exactly when $d \in \varpi C$; assume every element of $A$ is algebraic over $C$, that for $a$ in the maximal ideal of $A$ and $b \ne 0$ in $A$ some power $a^n$ is divisible by $b$, and that every $g \in \mathcal N_0$ differs from the image of some element of $C$ by a non-unit. Let $W$ be a complete discrete valuation domain with irreducible element $\pi$, $\sigma : W \to \widehat{\mathcal N_0}$ a ring homomorphism sending $\pi$ to the image of $\varpi$, $E \ge 1$, and $\iota$ a ring isomorphism of the completion $\widehat{\mathcal N_0}$ (at the maximal ideal of $\mathcal N_0$) with the crossing model $W[[U,V]]/(UV - \pi^E)$ carrying $\sigma$ to the constants; assume that an $f \in \mathcal N_0$ with nonzero first residue of order $n$ at $x_1$ satisfies $\iota(f) \equiv \gamma V^n \pmod{(\pi, U)}$ for some unit $\gamma$, and symmetrically with $U^n$ modulo $(\pi, V)$ for the second residue and $x_2$. Finally let $x, y \in \mathcal N_0$ with the first residue of $x$ zero and $\mathrm{ord}_{x_2}$ of its second residue equal to $1$, the second residue of $y$ zero and $\mathrm{ord}_{x_1}$ of its first residue equal to $1$, and $xy = \varpi^{E_0} u$ with $u$ a unit of $\mathcal N_0$ and $E_0 \in \mathbb{N}$. Then for every $c$ in the maximal ideal of $A$ with $c \ne 0$ such that $\varpi^{E_0} = cm$ for some $m$ in the maximal ideal of $A$, there is a place $P \in S$ with $P.\mathrm{evalAt}\, y = c$.
--
--   This is the existence half of the annulus axiom for the node of a semistable degeneration read through its function field: the node coordinate $y$ takes every value $c$ in the maximal ideal of $A$ satisfying the annulus condition $\varpi^{E_0} \in cA$ at some place of $F$ centred at the node. It is used in the construction of the attached annulus pair in [`AlgebraicCurve.exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates`](thm.html#AlgebraicCurve.exists_annulusPair_isAttached_of_ringEquiv_uvCrossingModel_of_nodeCoordinates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_NodeAnnulusEngine_exists_mem_and_evalAt_eq.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.UVCrossingModel

theorem AlgebraicCurve.NodeAnnulusEngine.exists_mem_and_evalAt_eq
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)

    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩 : Subring F)
    (h𝒩 : ∀ f : F, f ∈ 𝒩 ↔ f ∈ R₁.integers ∧ f ∈ R₂.integers ∧ ∀ P ∈ S, f ∈ P.toValuationSubring)
    (hval : ∀ f ∈ 𝒩, ∀ P ∈ S, P.evalAt f ∈ A)

    (hreg : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers), f ∈ 𝒩 →
      (R₁.residue ⟨f, h₁⟩ ≠ 0 → 0 ≤ x₁.ord (R₁.residue ⟨f, h₁⟩)) ∧
      (R₂.residue ⟨f, h₂⟩ ≠ 0 → 0 ≤ x₂.ord (R₂.residue ⟨f, h₂⟩)))
    (hord : ∀ (f : F) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
      R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
        {P : Place L F | P ∈ S ∧ P.ord f ≠ 0}.Finite ∧
        ∑ᶠ P ∈ S, P.ord f = x₁.ord (R₁.residue ⟨f, h₁⟩) + x₂.ord (R₂.residue ⟨f, h₂⟩))

    (𝒩₀ : Subring F) (h𝒩₀ : 𝒩₀ ≤ 𝒩) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]

    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))

    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)

    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)

    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)

    (hx₁r : x₁.IsRational) (hx₂r : x₂.IsRational)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))

    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥𝒩₀) (n : ℕ), R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥𝒩₀) (n : ℕ), R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).2.1⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, ((h𝒩 f).1 (h𝒩₀ f.2)).2.1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})

    (x y : ↥𝒩₀)
    (x_fst : R₁.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).1⟩ = 0)
    (x_snd : x₂.ord (R₂.residue ⟨x, ((h𝒩 x).1 (h𝒩₀ x.2)).2.1⟩) = 1)
    (y_snd : R₂.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).2.1⟩ = 0)
    (y_fst : x₁.ord (R₁.residue ⟨y, ((h𝒩 y).1 (h𝒩₀ y.2)).1⟩) = 1)
    (E₀ : ℕ) (u : ↥𝒩₀) (hu : IsUnit u)
    (hxy : x * y = ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ ^ E₀ * u) :
    ∀ c : ↥A, c ∈ maximalIdeal ↥A → (c : L) ≠ 0 →
      (∃ m ∈ maximalIdeal ↥A, (((ϖ : ↥C) : L) ^ E₀) = (c : L) * (m : L)) →
        ∃ P ∈ S, P.evalAt ((y : ↥𝒩₀) : F) = (c : L) := by sorry
