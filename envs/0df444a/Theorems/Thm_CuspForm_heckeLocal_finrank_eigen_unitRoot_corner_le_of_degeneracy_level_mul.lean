-- Prove2me | Theorems.Thm_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul
-- name    : CuspForm.heckeLocal.finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.082482+00:00
-- url     : https://prove2.me/theorems/98dce3fa-a45d-5cb1-b8b0-ff38987ff50f
-- title:
--   Eigen-rank bound across the degeneracy rung at p
-- statement:
--   Throughout, $\mathcal O$ is a complete discrete valuation ring of characteristic zero with finite residue field, $p$ is a prime with $p \neq 2$ and $p$ in the maximal ideal of $\mathcal O$, and $\bar\rho$ is a residual Galois representation over the residue field of $\mathcal O$ in the sense of the project's [`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22): a two-dimensional representation $\bar\rho.\rho$ of $\mathrm{Aut}(\overline{\mathbb Q}/\mathbb Q)$ on $\bar\rho.V$ factoring through a finite extension of $\mathbb Q$.
--
--   *Hypotheses on $\bar\rho$.* It is assumed absolutely irreducible (`habs`: the base change of $\bar\rho$ to an algebraic closure of the residue field has no invariant submodule other than $0$ and everything), and ordinary at $p$ (`hord`): viewing $\bar\rho$ as an adic representation over its coefficient field, for every valuation subring $P$ of $\overline{\mathbb Q}$ in which $p$ is a nonunit there is a free rank-one submodule $L$ of $\bar\rho.V$, spanned by the first member of a basis, stable under the decomposition group of $P$ and with the inertia subgroup of $P$ acting trivially on the quotient.
--
--   *Level and ramification data.* $S$ is a finite set of primes, all of whose members are prime (`hS`) and containing $p$ (`hpS`); $N$ is a nonzero level with $p \nmid N$ (`hpN`) all of whose prime divisors lie in $S$ (`hNS`). A second finite set $S_{\min} \subseteq S$ contains $p$ and satisfies: for primes $q \neq p$, $q \in S_{\min}$ exactly when $\bar\rho$ is ramified at $q$ (`hmin`, where unramifiedness at $q$ means that $\bar\rho.\rho$ kills the inertia subgroup of every valuation subring over $q$); every $q \in S_{\min}$ with $q \neq p$ divides $N$ (`hNmin`); every prime $q \neq p$ outside $S_{\min}$ dividing $N$ satisfies $q^2 \mid N$ (`hNunr`); and for $q \in S_{\min}$, $q \neq p$, inertia at $q$ acts with characteristic polynomial $(X-1)^2$ (`htame`).
--
--   *Auxiliary prime.* $r$ is a prime with $5 \le r$, $r \notin S$, $r \nmid Np$ and $p \nmid r-1$, subject to `hrρ`: for every valuation subring $P$ of $\overline{\mathbb Q}$ lying over $r$ and every $\sigma$ that is a Frobenius at $r$ for $P$ (acting as $x \mapsto x^r$ on the residue field of $P$), $\operatorname{tr}(\bar\rho.\rho(\sigma))^2 \neq (r+1)^2$.
--
--   *Hecke characters and $\mathcal O$-points.* Subject to the integrality hypotheses at levels $Np$ and $N$ in weight $2$ (the cusp forms with integral $q$-expansion coefficients span the full space over $\mathbb C$), $\theta_1$ and $\theta_0$ are ring homomorphisms from the weight-two Hecke algebras of level $Np$, respectively $N$, with the operators at primes of $S$ omitted, to the residue field of $\mathcal O$, each cutting out $\bar\rho$: for every prime $\ell$ not dividing the level and not in $S$, and every Frobenius $\sigma$ at $\ell$ for a valuation subring over $\ell$, the characteristic polynomial of $\bar\rho.\rho(\sigma)$ equals $X^2 - \theta_i(T_\ell)X + \ell$ (`hθ₁`, `hθ₀`). Write $\mathbb T(Np)_{\theta_1}$ and $\mathbb T(N)_{\theta_0}$ for the corresponding local Hecke algebras [`CuspForm.heckeLocal`](def/CuspForm_HeckeLocal.html#L131), the localisations of the $\mathcal O$-base-changed Hecke algebras at the primes determined by $\theta_1$, $\theta_0$, with canonical maps [`CuspForm.heckeLocal.π`](def/CuspForm_HeckeLocal.html#L151) from the Hecke algebras. Then $\pi_{T_0}$, $\pi_{T_1}$ are $\mathcal O$-algebra homomorphisms $\mathbb T(N)_{\theta_0} \to \mathcal O$ and $\mathbb T(Np)_{\theta_1} \to \mathcal O$ which agree on Hecke operators at primes $\ell \notin S$ with $\ell \nmid Np$ (`hπ`).
--
--   *The lower level.* $H_0$ is the subgroup of $(\mathbb Z/Nr)^\times$ consisting of the units whose image in $\mathbb Z/r$ is $1$ (`hH₀`). The coefficient module is $H^1(Nr, H_0; \mathcal O)$, the additive homomorphisms from the abelianisation-free group $\Gamma_{H_0}(Nr)$ written additively into $\mathcal O$, with the transfer-type Hecke operators `heckeT`, their lower-triangular variants `heckeTlower`, and the diamond operators `diamondRaw`. A commutative $\mathcal O$-algebra $\mathbb T_0$ acts on this module compatibly with $\mathcal O$, $S_0$ is an idempotent splitting of $\mathbb T_0$ (finitely many complete orthogonal idempotents $e_i$ together with maximal ideals $\mathfrak m_i$ exhausting the maximal ideals, with $e_i \in \mathfrak m_j$ iff $i \neq j$), $i_0$ is one of its indices, $M_0 := \mathrm{cornerSubmodule}(S_0.e\,i_0)$ is the image of the idempotent, assumed finite and free over $\mathcal O$, and $e_0$ identifies the corner ring $S_0.\mathrm{CornerRing}\,i_0$ with $\mathbb T(N)_{\theta_0}$ as $\mathcal O$-algebras.
--
--   The hypotheses at this level are: `hT₀`, that for primes $\ell \notin S$ with $\ell \nmid N$ and $\ell \nmid Nr$ the corner action of $e_0^{-1}(\pi(T_\ell))$ on $M_0$ is the Hecke operator $T_\ell$ at level $Nr$; `htp`, that a distinguished element $t_p$ of the corner ring is a unit and acts on $M_0$ both as `heckeT` at $p$ and as `heckeTlower` at $p$; `hocc₀`, that the $\ker(\pi_{T_0} \circ e_0)$-torsion submodule $M_0[\mathfrak p_0]$ of $M_0$ over the corner ring is nonzero; `hrk₀`, that $\operatorname{rank}_{\mathcal O} M_0 = \operatorname{rank}_{\mathcal O} M_0[\mathfrak p_0] \cdot \operatorname{rank}_{\mathcal O}(S_0.\mathrm{CornerRing}\,i_0)$; `hgen`, that every element of $\mathbb T_0$ acts through an element of the $\mathcal O$-subalgebra generated by the operator family [`CohCarrier.opFamily`](def/CohCarrier_Inst.html#L91) at level $Nr$; a family $t_{\mathrm{full}}$ of elements of $\mathbb T_0$ indexed by the generators [`CohCarrier.Gen`](def/CohCarrier_Inst.html#L13) of level $Nr$ away from $S$ which, for those generators that are not $U_q$ with $q \nmid N$, act as the corresponding operator of `opFamily` (`htfull`) and are congruent modulo $S_0.\mathfrak m\,i_0$ to scalars $c_{\mathrm{full}}$ in $\mathcal O$ (`hcfull`); `hcofull`, that any class $v$ for which, for each such generator $g$ and each $k$, some power of $t_{\mathrm{full}}(g) - c_{\mathrm{full}}(g)$ carries $v$ into $\mathfrak m_{\mathcal O}^k \cdot H^1(Nr,H_0;\mathcal O)$, already lies in $M_0$; `hfaith₀`, that the corner ring acts faithfully on $M_0$; and `hdia`, that every $\sigma \in \Gamma_0(Nr)$ acts trivially on $M_0$ through `diamondRaw`.
--
--   *Unit root.* An element $\tilde\alpha$ of the corner ring is given with `hαt`: $\tilde\alpha$ is a unit, $\tilde\alpha^2 - t_p\tilde\alpha + p = 0$, and $\tilde\alpha - t_p$ lies in the ideal generated by the image of the maximal ideal of $\mathcal O$.
--
--   *The upper level.* $H$ is the preimage of $H_0$ under the reduction $(\mathbb Z/Nrp)^\times \to (\mathbb Z/Nr)^\times$ (`hH`). Two commutative $\mathcal O$-algebras $\mathbb T_a$, $\mathbb T_1$, finite over $\mathcal O$, act on $H^1(Nrp, H; \mathcal O)$ compatibly with $\mathcal O$; $\iota : \mathbb T_a \to \mathbb T_1$ is an $\mathcal O$-algebra map inducing the same action (`hι`); $U \in \mathbb T_1$ acts as the Hecke operator $T_p$ at level $Nrp$ (`hU`); and $\mathbb T_1$ is generated over $\mathcal O$ by the image of $\iota$ together with $U$ (`hgen₁`). Idempotent splittings $S_a$, $S_1$ with indices $i_a$, $i_1$ are given, $e_1$ identifies $S_1.\mathrm{CornerRing}\,i_1$ with $\mathbb T(Np)_{\theta_1}$, and the corner submodules $M_a := \mathrm{cornerSubmodule}(S_a.e\,i_a)$ and $M_1 := \mathrm{cornerSubmodule}(S_1.e\,i_1)$ are finite and free over $\mathcal O$; $h_{1a}$ is a `LevelLE` datum for the degeneracy map of degree $1$ from level $(Nrp, \top)$ to $(Nrp, H)$.
--
--   *The package `hE`.* Together with families $t_A$ (indexed by the generators of level $Nr$ away from $S$) and $d_A$ (indexed by $(\mathbb Z/Nrp)^\times$) of elements of $\mathbb T_a$, the hypothesis `hE` is a conjunction of thirteen clauses, summarised here: the elements $t_A(g)$, for $g$ ranging over the $T_\ell$ generators and the $U_q$ with $q \mid N$ (the diamond generators being excluded), act as the corresponding Hecke operators at level $Nrp$ and are congruent to $c_{\mathrm{full}}(g)$ modulo $S_a.\mathfrak m\,i_a$; the $d_A(d)$ act as `diamondL` and are congruent to $1$ modulo $S_a.\mathfrak m\,i_a$; these elements generate $\mathbb T_a$ over $\mathcal O$; $M_a$ is contained in the image under the degree-one degeneracy map `iDegL` of the parabolic homomorphisms at level $(Nrp, \top)$ (those vanishing on elements of trace-square $4$); $\iota^{-1}(S_1.\mathfrak m\,i_1) = S_a.\mathfrak m\,i_a$ and $U \notin S_1.\mathfrak m\,i_1$; whenever $\tilde\alpha$ is congruent to $a \in \mathcal O$ modulo the maximal ideal of the corner ring at $i_0$, then $U - a \in S_1.\mathfrak m\,i_1$; $M_1 \subseteq M_a$; there is a surjective $\mathcal O$-algebra map $\varphi$ from $S_a.\mathrm{CornerRing}\,i_a$ onto $S_1.\mathrm{CornerRing}\,i_1$ compatible with the two corner actions on classes with the same underlying cohomology class, and the corner action of $e_1^{-1}(\pi(T_\ell))$ on $M_1$ is the Hecke operator $T_\ell$ at level $Nrp$ for primes $\ell \notin S$ with $\ell \nmid Np$ and $\ell \nmid Nrp$; the corner ring at $i_1$ acts faithfully on $M_1$; the $\ker(\pi_{T_1} \circ e_1)$-torsion submodule $M_1[\mathfrak p_1]$ is nonzero; $\operatorname{rank}_{\mathcal O} M_1 = \operatorname{rank}_{\mathcal O} M_1[\mathfrak p_1] \cdot \operatorname{rank}_{\mathcal O}(S_1.\mathrm{CornerRing}\,i_1)$; and the submodule $\ker(\pi_{T_1} \circ e_1) \cdot M_1$ is saturated, in the sense that $a \cdot m'$ lying in it for some nonzero $a \in \mathcal O$ forces $m'$ to lie in it.
--
--   *The two degeneracy legs.* `h1` and `hp'` are `LevelLE` data for the degeneracy maps of degree $1$ and degree $p$ from level $(Nr, H_0)$ to level $(Nrp, H)$; `hLa` says that both induced maps `iDegL` send $M_0$ into $M_a$; and `hLc` says that for every $m \in M_0$ the $\tilde\alpha$-stabilisation $\iota_1^{*}(\tilde\alpha \cdot m) - \iota_p^{*}(m)$ lies in $M_1$.
--
--   *Conclusion.* The $\mathcal O$-rank of the eigen-part upstairs is at most the $\mathcal O$-rank of the eigen-part downstairs:
--   $$\operatorname{rank}_{\mathcal O} M_1[\mathfrak p_1] \;\le\; \operatorname{rank}_{\mathcal O} M_0[\mathfrak p_0],$$
--   where $M_1[\mathfrak p_1]$ is the $\ker(\pi_{T_1} \circ e_1)$-torsion submodule of $M_1$ over $S_1.\mathrm{CornerRing}\,i_1$ and $M_0[\mathfrak p_0]$ the $\ker(\pi_{T_0} \circ e_0)$-torsion submodule of $M_0$ over $S_0.\mathrm{CornerRing}\,i_0$, both regarded as $\mathcal O$-modules by restriction of scalars.
--
--   The statement is the oldform half of the comparison of eigen-parts across the degeneracy rung at the residue characteristic $p$: it bounds the rank of the $\pi_{T_1}$-eigen-part of the ordinary unit-root corner at level $Nrp$ by that of the $\pi_{T_0}$-eigen-part at level $Nr$, the passage from level $Np$ to level $N$ in the level-lowering step at $p$. It is used by [`CuspForm.heckeLocal.exists_algHom_cornerRing_levelLowering_unitRoot_of_degeneracy_level_mul`](thm.html#CuspForm.heckeLocal.exists_algHom_cornerRing_levelLowering_unitRoot_of_degeneracy_level_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_heckeLocal_finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul.lean

import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CohCarrier_LevelPairing
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_CohCarrier_Lower
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_LocalConditions
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open Polynomial IsLocalRing CohCarrier IharaLemma IharaTower

theorem CuspForm.heckeLocal.finrank_eigen_unitRoot_corner_le_of_degeneracy_level_mul
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)] [CharZero 𝒪]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (habs : ρbar.IsAbsolutelyIrreducible)
    (hord : (GaloisRepAdic.ofResidualGaloisRep ρbar).IsOrdinaryAt p)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (hpS : p ∈ S)
    (N : ℕ) [NeZero N] [NeZero (N * p)] (hpN : ¬ p ∣ N) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)

    (Smin : Finset ℕ) (hpSmin : p ∈ Smin) (hSmin : Smin ⊆ S)
    (hmin : ∀ q : ℕ, q.Prime → q ≠ p → (q ∈ Smin ↔ ¬ ρbar.IsUnramifiedAt q))
    (hNmin : ∀ q ∈ Smin, q ≠ p → q ∣ N)
    (hNunr : ∀ q : ℕ, q.Prime → q ≠ p → q ∉ Smin → q ∣ N → q ^ 2 ∣ N)
    (htame : ∀ q ∈ Smin, q ≠ p → (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q)
    (r : ℕ) (hr : r.Prime) (hr5 : 5 ≤ r) (hrS : r ∉ S) (hrN : ¬ r ∣ N * p) (hr1 : ¬ p ∣ r - 1)

    (hrρ : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime r →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ r →
        LinearMap.trace (ResidueField 𝒪) ρbar.V (ρbar.ρ σ) ^ 2 ≠ ((r : ResidueField 𝒪) + 1) ^ 2)
    [Fact (CuspForm.HasIntegralStructure (N * p) 2)]
    (θ₁ : CuspForm.heckeAlgebra (N * p) 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N * p) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    [Fact (CuspForm.HasIntegralStructure N 2)]
    (θ₀ : CuspForm.heckeAlgebra N 2 (↑S : Set ℕ) →+* ResidueField 𝒪)
    (hθ₀ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) =
            X ^ 2 - C (θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) * X + C (ℓ : ResidueField 𝒪))
    (πT₀ : CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀ →ₐ[𝒪] 𝒪)
    (πT₁ : CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁ →ₐ[𝒪] 𝒪)
    (hπ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓ₁ : ¬ ℓ ∣ N * p) (hℓ₀ : ¬ ℓ ∣ N),
      πT₁ (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (CuspForm.heckeAlgebra.T hℓ hℓ₁ hℓS)) =
        πT₀ (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓ₀ hℓS)))
    (H₀ : Subgroup (ZMod (N * r))ˣ) [NeZero (N * r)]
    (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1)

    {𝕋₀ : Type} [CommRing 𝕋₀] [Algebra 𝒪 𝕋₀] [Module 𝕋₀ (H1 (N * r) H₀ 𝒪)] [IsScalarTower 𝒪 𝕋₀ (H1 (N * r) H₀ 𝒪)]
    (S₀ : IdempotentSplitting 𝕋₀) (i₀ : Fin S₀.n)
    (e₀ : S₀.CornerRing i₀ ≃ₐ[𝒪] CuspForm.heckeLocal N (↑S : Set ℕ) 𝒪 θ₀)
    [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))]
    [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))]
    (tp : S₀.CornerRing i₀)
    (hT₀ : ∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r)
        (m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))),
      ((e₀.symm (CuspForm.heckeLocal.π N (↑S : Set ℕ) 𝒪 θ₀ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
          : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ ℓ 𝒪 (m : H1 (N * r) H₀ 𝒪))
    (htp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩; IsUnit tp ∧ (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeT (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪)) ∧
      (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      ((tp • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪) = heckeTlower (N * r) H₀ p 𝒪 (m : H1 (N * r) H₀ 𝒪)))
    (hocc₀ : Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)) ↑(RingHom.ker (πT₀.comp e₀.toAlgHom)) ≠ ⊥)
    (hrk₀ : Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)) =
      Module.finrank 𝒪 (Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
        ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))) * Module.finrank 𝒪 (S₀.CornerRing i₀))
    (hgen : ∀ t : 𝕋₀, ∃ f ∈ Algebra.adjoin 𝒪 (Set.range (CohCarrier.opFamily (N * r) H₀ (↑S : Set ℕ) 𝒪)),
      ∀ m : H1 (N * r) H₀ 𝒪, t • m = f m)
    (tfull : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝕋₀)
    (htfull : ∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      ∀ m : H1 (N * r) H₀ 𝒪, tfull g • m = CohCarrier.opFamily (N * r) H₀ (↑S : Set ℕ) 𝒪 g m)
    (cfull : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝒪)
    (hcfull : ∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      tfull g - algebraMap 𝒪 𝕋₀ (cfull g) ∈ S₀.𝔪 i₀)
    (hcofull : ∀ v : H1 (N * r) H₀ 𝒪, (∀ g, (match g with | .U q _ _ => q ∣ N | _ => True) →
      ∀ k : ℕ, ∃ n : ℕ, ((tfull g - algebraMap 𝒪 𝕋₀ (cfull g)) ^ n) • v ∈
        ((IsLocalRing.maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 (H1 (N * r) H₀ 𝒪))) →
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
    (hfaith₀ : ∀ t : S₀.CornerRing i₀, (∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)), t • m = 0) → t = 0)

    (hdia : ∀ (σ : ↥(CongruenceSubgroup.Gamma0 (N * r))) (v : H1 (N * r) H₀ 𝒪),
      v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀) → diamondRaw (N * r) H₀ 𝒪 σ v = v)

    (αt : S₀.CornerRing i₀)
    (hαt : IsUnit αt ∧ αt * αt - tp * αt + algebraMap 𝒪 (S₀.CornerRing i₀) (p : 𝒪) = 0 ∧
      αt - tp ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 (S₀.CornerRing i₀)))

    [NeZero (N * r * p)] (H : Subgroup (ZMod (N * r * p))ˣ)
      (hH : H = H₀.comap (ZMod.unitsMap (dvd_mul_right (N * r) p)))
      {𝕋ₐ 𝕋₁ : Type} [CommRing 𝕋ₐ] [CommRing 𝕋₁] [Algebra 𝒪 𝕋ₐ] [Algebra 𝒪 𝕋₁]
      [Module 𝕋ₐ (H1 (N * r * p) H 𝒪)] [Module 𝕋₁ (H1 (N * r * p) H 𝒪)]
      [IsScalarTower 𝒪 𝕋ₐ (H1 (N * r * p) H 𝒪)] [IsScalarTower 𝒪 𝕋₁ (H1 (N * r * p) H 𝒪)]
      [Module.Finite 𝒪 𝕋ₐ] [Module.Finite 𝒪 𝕋₁]
      (ι : 𝕋ₐ →ₐ[𝒪] 𝕋₁) (hι : ∀ (t : 𝕋ₐ) (v : H1 (N * r * p) H 𝒪), ι t • v = t • v)
      (U : 𝕋₁) (hU : ∀ v : H1 (N * r * p) H 𝒪, U • v = heckeT (N * r * p) H p 𝒪 v)
      (hgen₁ : Algebra.adjoin 𝒪 (Set.range ι ∪ {U}) = ⊤)
      (Sₐ : IdempotentSplitting 𝕋ₐ) (iₐ : Fin Sₐ.n) (S₁ : IdempotentSplitting 𝕋₁) (i₁ : Fin S₁.n)
      (e₁ : S₁.CornerRing i₁ ≃ₐ[𝒪] CuspForm.heckeLocal (N * p) (↑S : Set ℕ) 𝒪 θ₁)
      [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))]
      [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))]
      [Module.Finite 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))]
      [Module.Free 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))]

      (h₁ₐ : LevelLE (N * r * p) (N * r * p) ⊤ H 1)
    (tA : CohCarrier.Gen (N * r) (↑S : Set ℕ) → 𝕋ₐ) (dA : (ZMod (N * r * p))ˣ → 𝕋ₐ)
    (hE :

      (∀ g : CohCarrier.Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) →
        ∀ v : H1 (N * r * p) H 𝒪, tA g • v = (match g with
            | .T ℓ hℓ _ _ => (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeT (N * r * p) H ℓ 𝒪 v)
            | .U q hq _ => (haveI : NeZero q := ⟨hq.ne_zero⟩; heckeT (N * r * p) H q 𝒪 v)
            | .dia _ => v)) ∧
      (∀ g : CohCarrier.Gen (N * r) (↑S : Set ℕ), (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False) →
        tA g - algebraMap 𝒪 𝕋ₐ (cfull g) ∈ Sₐ.𝔪 iₐ) ∧
      (∀ (d : (ZMod (N * r * p))ˣ) (v : H1 (N * r * p) H 𝒪), dA d • v = diamondL (N * r * p) H 𝒪 d v) ∧
      (∀ d : (ZMod (N * r * p))ˣ, dA d - 1 ∈ Sₐ.𝔪 iₐ) ∧
      Algebra.adjoin 𝒪 (tA '' {g | (match g with | .T _ _ _ _ => True | .U q _ _ => q ∣ N | .dia _ => False)} ∪ Set.range dA) = ⊤ ∧

      (∀ v : H1 (N * r * p) H 𝒪, v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ) →
        v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH (N * r * p) ⊤) 𝒪).map
          (iDegL (N * r * p) (N * r * p) ⊤ H 1 𝒪 𝒪 h₁ₐ)) ∧

      (S₁.𝔪 i₁).comap ι = Sₐ.𝔪 iₐ ∧ U ∉ S₁.𝔪 i₁ ∧

      (∀ a : 𝒪, αt - algebraMap 𝒪 (S₀.CornerRing i₀) a ∈ IsLocalRing.maximalIdeal (S₀.CornerRing i₀) →
        U - algebraMap 𝒪 𝕋₁ a ∈ S₁.𝔪 i₁) ∧
      (∀ v : H1 (N * r * p) H 𝒪, v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁) →
        v ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))  ∧

      (∃ φ : (Sₐ.CornerRing iₐ) →ₐ[𝒪] (S₁.CornerRing i₁), Function.Surjective φ ∧
        (∀ (t : (Sₐ.CornerRing iₐ)) (x : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))) (x₁ : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))),
          (x : H1 (N * r * p) H 𝒪) = x₁ → ((t • x : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))) : H1 (N * r * p) H 𝒪) = (φ t • x₁ : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)))) ∧
        (∀ (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N * p) (hℓS : ℓ ∉ (↑S : Set ℕ)) (hℓr : ¬ ℓ ∣ N * r * p)
            (m : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))),
          ((e₁.symm (CuspForm.heckeLocal.π (N * p) (↑S : Set ℕ) 𝒪 θ₁ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) • m
              : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))) : H1 (N * r * p) H 𝒪) = heckeT (N * r * p) H ℓ 𝒪 (m : H1 (N * r * p) H 𝒪))) ∧

      (∀ t : S₁.CornerRing i₁, (∀ m' : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)), t • m' = 0) → t = 0) ∧
      Submodule.torsionBySet (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)) ↑(RingHom.ker (πT₁.comp e₁.toAlgHom)) ≠ ⊥ ∧
      Module.finrank 𝒪 ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)) =
        Module.finrank 𝒪 (Submodule.torsionBySet (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))
          ↑(RingHom.ker (πT₁.comp e₁.toAlgHom))) * Module.finrank 𝒪 (S₁.CornerRing i₁)  ∧

      (∀ (a : 𝒪) (m' : ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))), a ≠ 0 →
        a • m' ∈ (RingHom.ker (πT₁.comp e₁.toAlgHom) • ⊤ : Submodule (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))).restrictScalars 𝒪 →
        m' ∈ (RingHom.ker (πT₁.comp e₁.toAlgHom) • ⊤ : Submodule (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))).restrictScalars 𝒪))

    (h1 : LevelLE (N * r) (N * r * p) H₀ H 1) (hp' : LevelLE (N * r) (N * r * p) H₀ H p)
    (hLa : ∀ (k : Fin 2) (v : H1 (N * r) H₀ 𝒪), v ∈ cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀) →
      ![iDegL (N * r) (N * r * p) H₀ H 1 𝒪 𝒪 h1, iDegL (N * r) (N * r * p) H₀ H p 𝒪 𝒪 hp'] k v
        ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (Sₐ.e iₐ))
    (hLc : ∀ m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀)),
      iDegL (N * r) (N * r * p) H₀ H 1 𝒪 𝒪 h1 ((αt • m : ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))) : H1 (N * r) H₀ 𝒪)
          - iDegL (N * r) (N * r * p) H₀ H p 𝒪 𝒪 hp' (m : H1 (N * r) H₀ 𝒪)
        ∈ cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁)) :
    Module.finrank 𝒪 ((Submodule.torsionBySet (S₁.CornerRing i₁) ↥(cornerSubmodule (M := H1 (N * r * p) H 𝒪) (S₁.e i₁))
        ↑(RingHom.ker (πT₁.comp e₁.toAlgHom))).restrictScalars 𝒪) ≤
      Module.finrank 𝒪 ((Submodule.torsionBySet (S₀.CornerRing i₀) ↥(cornerSubmodule (M := H1 (N * r) H₀ 𝒪) (S₀.e i₀))
        ↑(RingHom.ker (πT₀.comp e₀.toAlgHom))).restrictScalars 𝒪) := by sorry
