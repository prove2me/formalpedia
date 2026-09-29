-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero
-- name    : CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/fedcd79c-310c-5bb6-8826-8229f4c48109
-- title:
--   Čerednik–Drinfeld equivariant uniformisation at both ramified primes
-- statement:
--   **Arithmetic data.** Natural numbers $N$, $q$, $q'$ are given with $N \neq 0$ and $N$ squarefree, $q$ and $q'$ prime, $q \nmid N$, $q' \nmid N$, $q' \neq q$ and $5 \le q$, $5 \le q'$; a further non-zero natural number $D$ is given with $6Nqq' \mid D$. Two valuation subrings of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` are fixed: $A_1$ with `A₁.LiesOverPrime q'` (that is, $q'$ is a non-unit of $A_1$) and $A_2$ with `A₂.LiesOverPrime q` (that is, $q$ is a non-unit of $A_2$).
--
--   **The definite datum at $q'$ (subscript $2$).** Rationals $a_2, b_2$ are given with `IsDefiniteRamifiedExactlyAt (a := a₂) (b := b₂) q`, i.e. $a_2 < 0$, $b_2 < 0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the completion $\mathbb{H}[\mathbb{Q}, a_2, b_2] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $q \in v$. Two $\mathbb{Z}$-submodules $\Lambda_2, R_2$ of this quaternion algebra are given with $\Lambda_2$ a maximal order, $R_2$ an Eichler order of level $N$ (an intersection of two maximal orders, of relative index $N$ in the first of them) and $R_2 \le \Lambda_2$. A unit $n_2$ of $\mathbb{H}[\mathbb{Q}, a_2, b_2] \otimes_{\mathbb{Q}} \mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ is given lying in `primeHeckeSet R₂ q'` (its coordinates lie in the adelic box of $R_2$, $q' \cdot n_2^{-1}$ lies in that box, while $n_2^{-1}$ and $(q')^{-1} n_2$ do not), and the following are assumed of it: `hS₂`, that the meet order $R_2 \cap n_2 R_2 n_2^{-1}$ is an Eichler order of level $Nq'$; `hnorm₂`, that $n_2$ normalises this meet order; `hsq₂`, that the shift $x \mapsto x n_2$ on the class set $\mathrm{ClassSet}$ of the finite-idelic stabiliser of the meet order is an involution; and `hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂`, the four clauses asserting that the edge Hecke matrices `classSetEdgeHecke N q' Λ₂ R₂ n₂ ℓ` pairwise commute, that the vertex Hecke matrices `classSetVertexHecke N Λ₂ ℓ` pairwise commute, that for $\ell \neq q'$ the two degeneracy pushforwards intertwine the edge and vertex matrices, and that the edge matrices preserve the kernel of the pair of pushforwards.
--
--   **The definite datum at $q$ (subscript $1$).** Symmetrically, rationals $a_1, b_1$ are given with $\mathbb{H}[\mathbb{Q}, a_1, b_1]$ definite and ramified exactly at $q'$, a maximal order $\Lambda_1$ and an Eichler order $R_1$ of level $N$ with $R_1 \le \Lambda_1$, and a finite-idelic unit $n_1 \in$ `primeHeckeSet R₁ q` such that the meet order $R_1 \cap n_1 R_1 n_1^{-1}$ is Eichler of level $Nq$, is normalised by $n_1$, the shift by $n_1$ on the corresponding class set is an involution, and `hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁` holds (the same four clauses, with $q$ in place of $q'$).
--
--   **The indefinite datum.** Rationals $a, b$ are given with `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and $\mathbb{H}[\mathbb{Q}, a, b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a division algebra exactly when $q \in v$ or $q' \in v$; an Eichler order $R$ of level $N$ in it; and an injective $\mathbb{Q}$-algebra map $\iota : \mathbb{H}[\mathbb{Q}, a, b] \to M_2(\mathbb{R})$.
--
--   **Conclusion.** There exist a maximal order $\Lambda$ with $R \le \Lambda$, a model
--   $$M : \mathtt{ShimuraCurveModel}\ R\ \iota\ \bigl(\ell \mapsto \text{if } \ell \mid N \text{ then } \mathtt{levelHeckeUSet}\ \Lambda\ R\ \ell \text{ else } \mathtt{primeHeckeSet}\ R\ \ell\bigr),$$
--   where `levelHeckeUSet Λ R ℓ` consists of those $h \in$ `primeHeckeSet R ℓ` with $hRh^{-1} \neq R$ and $R \not\le h\Lambda h^{-1}$, and a family of signs $\varepsilon : \mathtt{Nat.Primes} \to \mathbb{Z}^\times$, such that the following hold.
--
--   (i) $\varepsilon_\ell = 1$ for every prime $\ell$ with $\ell \neq q$ and $\ell \neq q'$.
--
--   (ii) For every prime $p$, `M.GoodReductionOutside p (D * p)`: for every prime $\ell \nmid Dp$ and every valuation subring $B$ of $\overline{\mathbb{Q}}$ lying over $\ell$, every element of the inertia subgroup of $B$ over $\mathbb{Q}$ fixes every $p$-torsion point of the abelian group `M.J` under `M.galJ`; and for every such $\ell$ and $B$, every $\sigma$ which is a Frobenius at $\ell$ for $B$ (i.e. lies in the decomposition subgroup and induces $x \mapsto x^{\ell}$ on the residue field) satisfies the Eichler–Shimura relation $\sigma^2 t - T_\ell(\sigma t) + \ell\, t = 0$ on $p$-torsion $t \in$ `M.J`, with $T_\ell =$ `M.heckeJ (heckeGen ⟨ℓ, _⟩)`.
--
--   (iii) *The package at $q'$.* There exist an abelian group $T_1$, a homomorphism $\mathtt{galT₁}$ from the decomposition subgroup $A_1.\mathrm{decompositionSubgroup}\ \mathbb{Q}$ to the additive automorphisms of $T_1$, a parity character $\chi_1$ from that decomposition subgroup to $\mathrm{Multiplicative}(\mathbb{Z}/2)$, a homomorphism $\mathtt{actZ₁}$ from it to the $\mathbb{Z}$-linear automorphisms of the ribbon kernel $Z_2 := \mathtt{ribbonKernel}(\mathtt{classSetDegeneracyData}\ R_2\ n_2)$ — the intersection of the kernels of the two pushforwards of the degeneracy datum whose edge set is the class set of the stabiliser of $R_2 \cap n_2R_2n_2^{-1}$, whose vertex set is the class set of the stabiliser of $R_2$, whose two maps are the forgetful map and the shift by $n_2$, and whose weights are the unit weights `classWeight` of the meet order — an additive map $\iota_{T_1} : M.J \to T_1$, and an equivariant uniformisation
--   $$\mathcal{U} : \mathtt{Mumford.EquivariantUniformization}\ q'\ (\mathtt{classSetDegeneracyData}\ R_2\ n_2)\ A_1\ \mathtt{hA₁}\ T_1\ (A_1.\mathrm{decompositionSubgroup}\ \mathbb{Q})\ \mathrm{id}\ \mathtt{actZ₁}\ \mathtt{galT₁},$$
--   that is: an intermediate field $K$ of $\mathbb{Q}$ in the completion of $A_1$'s valuation together with a homomorphism $\mathrm{ord}$ on $K^\times$ computing valuations as powers of $v(q')$, invariance of $K$ under automorphisms extending inertia elements, existence of $n$-th roots in $K^\times$ of units of $\mathrm{ord}$ zero for $n$ prime to $q'$, a period datum $P$ over $K$ (a symmetric $\mathbb{Z}$-bilinear form $Q$ on $Z_2$ with values in $\mathrm{Additive}\,K^\times$ whose $\mathrm{ord}$ is the ribbon Gram pairing), and a surjection $\mathcal{U}.\mathtt{eFull}$ from the torus points $Z_2 \to \mathrm{Additive}\,C^\times$ ($C$ the completion) onto $T_1$ with kernel the period lattice, compatibly with the given actions. These satisfy:
--
--   (1) $\chi_1$ is trivial on elements of the decomposition subgroup whose underlying automorphism lies in the inertia subgroup of $A_1$ over $\mathbb{Q}$;
--
--   (2) $\chi_1 \varphi \neq 1$ for every $\varphi$ whose underlying automorphism is a Frobenius at $q'$ for $A_1$;
--
--   (3) $\mathtt{actZ₁}\,\tau = 1$ whenever $\chi_1 \tau = 1$;
--
--   (4) if $\chi_1\tau \neq 1$ then for every $x \in Z_2$ the function underlying $\mathtt{actZ₁}\,\tau\,x$ on the edge class set is $c \mapsto -x(\mathtt{classSetShift}\ \_\ n_2\ c)$;
--
--   (5) for all $x, y, x', y' \in Z_2$, if $x'$ is the function $c \mapsto -x(\mathtt{classSetShift}\ \_\ n_2\ c)$ and $y'$ is the function $c \mapsto -y(\mathtt{classSetShift}\ \_\ n_2\ c)$, then $\mathcal{U}.P.Q\,x'\,y' = \mathcal{U}.P.Q\,x\,y$;
--
--   (6) $\mathcal{U}.P$ is Hecke-adjointable for $\mathtt{classSetHeckeData}\ N\ q'\ \Lambda_2\ R_2\ n_2$: for every prime $\ell$ and every $y \in Z_2$ there is $y' \in Z_2$ with $Q\,y\,(\mathtt{heckeKernelMap}\ H\ \ell\ z) = Q\,y'\,z$ for all $z \in Z_2$;
--
--   (7) $\iota_{T_1}$ is injective;
--
--   (8) every element of finite additive order in $T_1$ lies in the range of $\iota_{T_1}$;
--
--   (9) $\iota_{T_1}(M.\mathtt{galJ}\,\tau\,c) = \mathtt{galT₁}\,\tau\,(\iota_{T_1} c)$ for every $\tau$ in the decomposition subgroup and $c \in M.J$;
--
--   (10) for every prime $\ell$, every torus point $u$ in the subset $\mathcal{U}.P.U$ and every $c \in M.J$ with $\mathcal{U}.\mathtt{eFull}\,u = \iota_{T_1} c$, one has $\mathcal{U}.\mathtt{eFull}\bigl(\mathcal{U}.P.\mathtt{precomp}\,(\mathtt{heckeKernelMap}\ (\mathtt{classSetHeckeData}\ N\ q'\ \Lambda_2\ R_2\ n_2)\ \ell)\,u\bigr) = \iota_{T_1}\bigl(M.\mathtt{heckeJSigned}\ \varepsilon\ (\mathtt{heckeGen}\ \ell)\ c\bigr)$, the right-hand Hecke operator being the sign-twisted one, $\varepsilon_\ell T_\ell$.
--
--   (iv) *The package at $q$.* The same list of assertions, with $A_2$, $q$, the degeneracy datum $\mathtt{classSetDegeneracyData}\ R_1\ n_1$, the shift by $n_1$ and the Hecke datum $\mathtt{classSetHeckeData}\ N\ q\ \Lambda_1\ R_1\ n_1$ in place of $A_1$, $q'$, $\mathtt{classSetDegeneracyData}\ R_2\ n_2$, the shift by $n_2$ and $\mathtt{classSetHeckeData}\ N\ q'\ \Lambda_2\ R_2\ n_2$: an abelian group $T_2$, homomorphisms $\mathtt{galT₂}$, $\chi_2$, $\mathtt{actZ₂}$, an additive map $\iota_{T_2} : M.J \to T_2$ and an equivariant uniformisation of $T_2$ over that datum with $\chi_2$ trivial on inertia and non-trivial on Frobenius elements at $q$, the action on the ribbon kernel trivial at even parity and equal to $x \mapsto -x \circ (\text{shift by } n_1)$ at odd parity, invariance of $Q$ under this involution in both arguments, Hecke-adjointability, injectivity of $\iota_{T_2}$ with image containing all torsion of $T_2$, Galois equivariance of $\iota_{T_2}$, and the same sign-twisted Hecke compatibility on $\mathcal{U}.P.U$.
--
--   The sign family $\varepsilon$ and the model $M$ are common to the two packages (iii) and (iv).
--
--   This is the Čerednik–Drinfeld $p$-adic uniformisation of the Shimura curve attached to an indefinite quaternion algebra ramified exactly at $q$ and $q'$ with Eichler level $N$, set up simultaneously at both primes of the discriminant and in the form of a Mumford period uniformisation of an abelian group receiving the curve's Jacobian points, with the Atkin–Lehner parity character, the Frobenius action on the character group and Hecke compatibility recorded. It is the input to the corresponding statement for the $p$-torsion period uniformisation, which feeds the level-lowering argument at $q$ and $q'$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_EquivariantUniformization
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField MatrixGroups
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld
open ModularCurve

theorem CerednikDrinfeld.exists_shimuraCurveModel_goodReduction_and_equivariantUniformization_pair_of_six_mul_dvd_of_neZero
    {N q q' : ℕ} [NeZero N] (hN : Squarefree N) [Fact q.Prime] [Fact q'.Prime]
    (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    (D : ℕ) [NeZero D] (hD : 6 * N * q * q' ∣ D)
    (hq5 : 5 ≤ q) (hq'5 : 5 ≤ q')
    (A₁ : ValuationSubring (AlgebraicClosure ℚ)) (hA₁ : A₁.LiesOverPrime q')
    (A₂ : ValuationSubring (AlgebraicClosure ℚ)) (hA₂ : A₂.LiesOverPrime q)

    {a₂ b₂ : ℚ} (hdef₂ : IsDefiniteRamifiedExactlyAt (a := a₂) (b := b₂) q)
    (Λ₂ R₂ : Submodule ℤ ℍ[ℚ, a₂, b₂]) (hΛ₂ : IsMaximalOrder Λ₂) (hR₂ : IsEichlerOrder R₂ N) (hRΛ₂ : R₂ ≤ Λ₂)
    (n₂ : (ℍ[ℚ, a₂, b₂] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₂ : n₂ ∈ primeHeckeSet R₂ q')
    (hS₂ : IsEichlerOrder (meetOrder R₂ n₂) (N * q'))
    (hnorm₂ : Submodule.conjByFiniteIdele (meetOrder R₂ n₂) n₂ = meetOrder R₂ n₂)
    (hsq₂ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)),
      classSetShift _ n₂ (classSetShift _ n₂ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₂))]
    (hlaws₂ : ClassSetHeckeLaws N q' Λ₂ R₂ n₂)

    {a₁ b₁ : ℚ} (hdef₁ : IsDefiniteRamifiedExactlyAt (a := a₁) (b := b₁) q')
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ q)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * q))
    (hnorm₁ : Submodule.conjByFiniteIdele (meetOrder R₁ n₁) n₁ = meetOrder R₁ n₁)
    (hsq₁ : ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)),
      classSetShift _ n₁ (classSetShift _ n₁ x) = x)
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)))]
    [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R₁))]
    (hlaws₁ : ClassSetHeckeLaws N q Λ₁ R₁ n₁)

    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ (Λ : Submodule ℤ ℍ[ℚ, a, b]) (_ : IsMaximalOrder Λ) (_ : R ≤ Λ),
    ∃ M : ShimuraCurveModel R ι (fun ℓ => if ℓ ∣ N then levelHeckeUSet Λ R ℓ else primeHeckeSet R ℓ),
      ∃ ε : Nat.Primes → ℤˣ, (∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q → (ℓ : ℕ) ≠ q' → ε ℓ = 1) ∧
      (∀ p : ℕ, p.Prime → M.GoodReductionOutside p (D * p)) ∧

      (∃ (T₁ : Type) (_ : AddCommGroup T₁)
         (galT₁ : ↥(A₁.decompositionSubgroup ℚ) →* AddAut T₁)
         (χ₁ : ↥(A₁.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (actZ₁ : ↥(A₁.decompositionSubgroup ℚ) →* (↥(ribbonKernel (classSetDegeneracyData R₂ n₂)) ≃ₗ[ℤ] ↥(ribbonKernel (classSetDegeneracyData R₂ n₂))))
         (ιT₁ : M.J →+ T₁)
         (𝒰 : Mumford.EquivariantUniformization q' (classSetDegeneracyData R₂ n₂) A₁ hA₁ T₁
            ↥(A₁.decompositionSubgroup ℚ) (MonoidHom.id _) actZ₁ galT₁),

        (∀ τ : ↥(A₁.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₁.inertiaSubgroupIn ℚ → χ₁ τ = 1) ∧
        (∀ φ : ↥(A₁.decompositionSubgroup ℚ),
          A₁.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q' → χ₁ φ ≠ 1) ∧

        (∀ τ, χ₁ τ = 1 → actZ₁ τ = 1) ∧
        (∀ τ, χ₁ τ ≠ 1 → ∀ x : ↥(ribbonKernel (classSetDegeneracyData R₂ n₂)),
          ((actZ₁ τ x : ↥(ribbonKernel (classSetDegeneracyData R₂ n₂))) : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)) → ℤ) =
            fun c => - (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)) → ℤ) (classSetShift _ n₂ c)) ∧

        (∀ x y x' y' : ↥(ribbonKernel (classSetDegeneracyData R₂ n₂)),
          ((x' : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)) → ℤ) = fun c => - (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)) → ℤ) (classSetShift _ n₂ c)) →
          ((y' : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)) → ℤ) = fun c => - (y : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₂ n₂)) → ℤ) (classSetShift _ n₂ c)) →
            𝒰.P.Q x' y' = 𝒰.P.Q x y) ∧

        𝒰.P.HeckeAdjointable (classSetHeckeData N q' Λ₂ R₂ n₂) ∧

        Function.Injective ιT₁ ∧
        (∀ t : T₁, IsOfFinAddOrder t → t ∈ ιT₁.range) ∧
        (∀ (τ : ↥(A₁.decompositionSubgroup ℚ)) (c : M.J),
          ιT₁ (M.galJ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) c) = galT₁ τ (ιT₁ c)) ∧

        (∀ (ℓ : Nat.Primes) (u : 𝒰.P.TorusPoints) (c : M.J), u ∈ 𝒰.P.U → 𝒰.eFull u = ιT₁ c →
          𝒰.eFull (𝒰.P.precomp (heckeKernelMap (classSetHeckeData N q' Λ₂ R₂ n₂) ℓ) u) = ιT₁ (M.heckeJSigned ε (heckeGen ℓ) c))) ∧

      (∃ (T₂ : Type) (_ : AddCommGroup T₂)
         (galT₂ : ↥(A₂.decompositionSubgroup ℚ) →* AddAut T₂)
         (χ₂ : ↥(A₂.decompositionSubgroup ℚ) →* Multiplicative (ZMod 2))
         (actZ₂ : ↥(A₂.decompositionSubgroup ℚ) →* (↥(ribbonKernel (classSetDegeneracyData R₁ n₁)) ≃ₗ[ℤ] ↥(ribbonKernel (classSetDegeneracyData R₁ n₁))))
         (ιT₂ : M.J →+ T₂)
         (𝒰 : Mumford.EquivariantUniformization q (classSetDegeneracyData R₁ n₁) A₂ hA₂ T₂
            ↥(A₂.decompositionSubgroup ℚ) (MonoidHom.id _) actZ₂ galT₂),

        (∀ τ : ↥(A₂.decompositionSubgroup ℚ),
          (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ A₂.inertiaSubgroupIn ℚ → χ₂ τ = 1) ∧
        (∀ φ : ↥(A₂.decompositionSubgroup ℚ),
          A₂.IsFrobeniusAt (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) q → χ₂ φ ≠ 1) ∧

        (∀ τ, χ₂ τ = 1 → actZ₂ τ = 1) ∧
        (∀ τ, χ₂ τ ≠ 1 → ∀ x : ↥(ribbonKernel (classSetDegeneracyData R₁ n₁)),
          ((actZ₂ τ x : ↥(ribbonKernel (classSetDegeneracyData R₁ n₁))) : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)) → ℤ) =
            fun c => - (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)) → ℤ) (classSetShift _ n₁ c)) ∧

        (∀ x y x' y' : ↥(ribbonKernel (classSetDegeneracyData R₁ n₁)),
          ((x' : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)) → ℤ) = fun c => - (x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)) → ℤ) (classSetShift _ n₁ c)) →
          ((y' : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)) → ℤ) = fun c => - (y : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R₁ n₁)) → ℤ) (classSetShift _ n₁ c)) →
            𝒰.P.Q x' y' = 𝒰.P.Q x y) ∧

        𝒰.P.HeckeAdjointable (classSetHeckeData N q Λ₁ R₁ n₁) ∧

        Function.Injective ιT₂ ∧
        (∀ t : T₂, IsOfFinAddOrder t → t ∈ ιT₂.range) ∧
        (∀ (τ : ↥(A₂.decompositionSubgroup ℚ)) (c : M.J),
          ιT₂ (M.galJ (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) c) = galT₂ τ (ιT₂ c)) ∧

        (∀ (ℓ : Nat.Primes) (u : 𝒰.P.TorusPoints) (c : M.J), u ∈ 𝒰.P.U → 𝒰.eFull u = ιT₂ c →
          𝒰.eFull (𝒰.P.precomp (heckeKernelMap (classSetHeckeData N q Λ₁ R₁ n₁) ℓ) u) = ιT₂ (M.heckeJSigned ε (heckeGen ℓ) c))) := by sorry
