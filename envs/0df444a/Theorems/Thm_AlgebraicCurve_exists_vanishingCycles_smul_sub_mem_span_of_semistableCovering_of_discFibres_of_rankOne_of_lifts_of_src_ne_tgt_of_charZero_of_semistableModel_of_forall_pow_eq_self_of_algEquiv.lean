-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_vanishingCycles_smul_sub_mem_span_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_forall_pow_eq_self_of_algEquiv
-- name    : AlgebraicCurve.exists_vanishingCycles_smul_sub_mem_span_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_forall_pow_eq_self_of_algEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/dd7efda5-e055-562e-9777-e29c20ef4b96
-- title:
--   Vanishing cycles span the monodromy differences, naturally
-- statement:
--   Let $L$ be an algebraically closed field of characteristic $0$, $A \subseteq L$ a valuation subring, and $\pi \in A$ a nonzero element of the maximal ideal; assume the rank-one condition that for every $x \in L^{\times}$ and every $y$ in the maximal ideal some power $y^{n}$ has valuation at most that of $x$. Let $F$ be a field extension of $L$ which is a curve over $L$ (finitely supported principal divisors of degree zero, finite residue extensions, $\Omega_{F/L}$ free of rank $1$) and essentially of finite type. Let $n, m \in \mathbb{N}$, let $\bar F_i$ ($i \in \mathrm{Fin}\,n$) be fields over the residue field $k$ of $A$, all of whose places are rational, let $C_i$ be component charts of $F$ with values in $\bar F_i$ (a valuation subring of $F$ with a surjective residue map onto $\bar F_i$, a set of places `dom`, a finite set of nodes, and a place map, satisfying the chart axioms), all places in $(C_i).\mathrm{dom}$ being rational, and let $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$) be annuli with source and target indices $\mathrm{src}\,e, \mathrm{tgt}\,e$, attaching nodes $x_s(e) \in (C_{\mathrm{src}\,e}).\mathrm{nodes}$, $x_t(e) \in (C_{\mathrm{tgt}\,e}).\mathrm{nodes}$, and weights $w(e) \in \mathbb{N}$. The combinatorial hypotheses are: $\mathrm{An}'_e$ has the same domain and the same (nonzero) modulus as $\mathrm{An}_e$ and the product of the two parameters is the image of that modulus; each modulus is a unit times $\pi^{w(e)}$; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}\,e}$ at $x_s(e)$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}\,e}$ at $x_t(e)$ in the sense of `IsAttached`; every node of every chart is an end of some annulus, and the map from $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$ sending the two copies of $e$ to $(\mathrm{src}\,e, x_s(e))$, resp. $(\mathrm{tgt}\,e, x_t(e))$, is injective over nodes; every place of $F/L$ lies either in exactly one chart domain and no annulus domain, or in exactly one annulus domain and no chart domain; over each non-node place $Q$ of $\bar F_i$ there is a chart function $T$ whose residue has $\mathrm{ord}_Q = 1$, which is integral with value in the maximal ideal at every place of the chart domain above $Q$, and such that each $c$ in the maximal ideal of $A$ is the value of $T$ at exactly one such place; and the genus relation $g(F/L) + n = \sum_i g(\bar F_i/k) + m + 1$. Let $S$ be a set of semilinear automorphisms of $F$ (pairs consisting of a ring automorphism of $F$ and one of $L$, compatible with $L \to F$) each of which stabilises $A$, fixes $\pi$, induces the identity on $k$, preserves every chart domain and annulus domain, fixes the parameters of all $\mathrm{An}_e$ and $\mathrm{An}'_e$, preserves the chart integers and induces the identity on each $\bar F_i$ via the residue map, and commutes with every place map; assume every automorphism of $L$ stabilising $A$, fixing $\pi$ and inducing the identity on $k$ is the base automorphism of some element of $S$. Let $\ell$ be a prime which is a unit in $k$, assume some element of $S$ moves some $\ell$-th root of $\pi$, and assume $V := \mathbb{Q}_{\ell} \otimes_{\mathbb{Z}_{\ell}} T_{\ell}(\mathrm{Pic}^{0}(F/L))$ is finite-dimensional over $\mathbb{Q}_{\ell}$. Assume each $\bar F_i$ is a curve over $k$ and essentially of finite type, let $M$ be a semistable model of the data over $A$ together with a descent $D$ of $M$ to a Noetherian Henselian local subring, and assume every element of $k$ satisfies $a^{p^{n}} = a$ for some $n > 0$ when $k$ has characteristic $p$. Then there is a family $vc : \mathrm{Fin}\,m \to V$ such that, first, for every $s \in S$ and every $v \in V$ the difference $\rho(s)v - v$ lies in the $\mathbb{Q}_{\ell}$-span of the range of $vc$, where $\rho$ is the action of the semilinear automorphism group on $V$; and second, $vc$ is natural: for every $L$-algebra automorphism $\tau$ of $F$ and all permutations $\sigma_0$ of $\mathrm{Fin}\,n$, $\sigma_1$ of $\mathrm{Fin}\,m$ with $\mathrm{src}(\sigma_1 e) = \sigma_0(\mathrm{src}\,e)$ and $\mathrm{tgt}(\sigma_1 e) = \sigma_0(\mathrm{tgt}\,e)$, such that $\tau$ matches chart domains, chart integers and annulus domains along $\sigma_0$ and $\sigma_1$, and provided $\mathrm{src}\,e \neq \mathrm{tgt}\,e$ for all $e$, one has $\rho(\tau)(vc\,e) = vc(\sigma_1 e)$ for every $e$.
--
--   This is the vanishing-cycle (Picard–Lefschetz) description of the monodromy on the rational $\ell$-adic Tate module of the Jacobian of a semistable curve: the cycle classes of the $m$ annuli of the covering span all differences $\rho(s)v - v$ for the inertia-type automorphisms in $S$, and the family of these classes is permuted by automorphisms of $F$ that permute the components and annuli. It is used in the full-level modular-curve statements bounding the image of $\rho(\sigma) - 1$ by the span of the unipotent-fixed vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_vanishingCycles_smul_sub_mem_span_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_forall_pow_eq_self_of_algEquiv.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open scoped TensorProduct

theorem
    AlgebraicCurve.exists_vanishingCycles_smul_sub_mem_span_of_semistableCovering_of_discFibres_of_rankOne_of_lifts_of_src_ne_tgt_of_charZero_of_semistableModel_of_forall_pow_eq_self_of_algEquiv
    {L : Type} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type) [Field F] [Algebra L F]
    (n m : ℕ) (Fbar : Fin n → Type) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : Fin m → Annulus A F) (src tgt : Fin m → Fin n)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : Fin m → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + n = (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + m + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (S : Set (SemilinearAut L F))
    (hS : ∀ s ∈ S, (∀ a : L, a ∈ A ↔ SemilinearAut.baseAut s a ∈ A) ∧ SemilinearAut.baseAut s (π : L) = (π : L) ∧
      (∀ (a : A) (h : SemilinearAut.baseAut s (a : L) ∈ A),
        IsLocalRing.residue A ⟨SemilinearAut.baseAut s (a : L), h⟩ = IsLocalRing.residue A a) ∧
      (∀ i, ∀ P ∈ (C i).dom, s • P ∈ (C i).dom) ∧ (∀ e, ∀ P ∈ (An e).dom, s • P ∈ (An e).dom) ∧
      (∀ e, s • (An e).param = (An e).param) ∧ (∀ e, s • (An' e).param = (An' e).param) ∧
      (∀ i, ∀ f : F, ∀ hf : f ∈ (C i).integers, ∃ hf' : s • f ∈ (C i).integers,
        (C i).residue ⟨s • f, hf'⟩ = (C i).residue ⟨f, hf⟩) ∧
      (∀ i, ∀ P ∈ (C i).dom, (C i).placeMap (s • P) = (C i).placeMap P))
    (hSlift : ∀ σ : L ≃+* L, (∀ a : L, a ∈ A ↔ σ a ∈ A) → σ (π : L) = (π : L) →
      (∀ (a : A) (h : σ (a : L) ∈ A), IsLocalRing.residue A ⟨σ (a : L), h⟩ = IsLocalRing.residue A a) →
      ∃ s ∈ S, SemilinearAut.baseAut s = σ)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit ((ℓ : ℕ) : IsLocalRing.ResidueField A))
    (hSℓ : ∃ s ∈ S, ∃ r : L, r ^ ℓ = (π : L) ∧ SemilinearAut.baseAut s r ≠ r)
    [FiniteDimensional ℚ_[ℓ] (ModularCurve.RationalTateModule ℓ (Pic0 L F))]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : AlgebraicCurve.SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (hκ : ∀ p : ℕ, p.Prime → CharP (IsLocalRing.ResidueField A) p →
      ∀ a : IsLocalRing.ResidueField A, ∃ n : ℕ, 0 < n ∧ a ^ (p ^ n) = a)
    :
    ∃ vc : Fin m → ModularCurve.RationalTateModule ℓ (Pic0 L F),
      (∀ s ∈ S, ∀ w : ModularCurve.RationalTateModule ℓ (Pic0 L F),
        ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) s w - w ∈ Submodule.span ℚ_[ℓ] (Set.range vc)) ∧
      ∀ (τ : F ≃ₐ[L] F) (σ₀ : Equiv.Perm (Fin n)) (σ₁ : Equiv.Perm (Fin m)),
        (∀ e, src (σ₁ e) = σ₀ (src e)) → (∀ e, tgt (σ₁ e) = σ₀ (tgt e)) →
        (∀ i, ∀ P : Place L F, P ∈ (C i).dom ↔ SemilinearAut.ofAlgAut τ • P ∈ (C (σ₀ i)).dom) →
        (∀ i, ∀ f : F, f ∈ (C i).integers ↔ τ f ∈ (C (σ₀ i)).integers) →
        (∀ e, ∀ P : Place L F, P ∈ (An e).dom ↔ SemilinearAut.ofAlgAut τ • P ∈ (An (σ₁ e)).dom) →
        (∀ e, src e ≠ tgt e) →
        ∀ e, ModularCurve.rationalGaloisRep ℓ (Pic0 L F) (SemilinearAut L F) (SemilinearAut.ofAlgAut τ) (vc e) = vc (σ₁ e) := by sorry
