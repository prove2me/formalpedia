-- Prove2me | Theorems.Thm_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
-- name    : CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/c5a5420e-8083-5dec-9ef1-4a362100e01c
-- title:
--   Atkin–Lehner–Li basis of S_k(Γ_H(M))
-- statement:
--   Let $M \ge 1$, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $k$ be an integer; write $\Gamma_H(M)$ for the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H$ under the lower-right-entry map $\Gamma_0(M) \to (\mathbb{Z}/M)^\times$. The assertion is that there exist a natural number $n$, levels $L_i \mid M$ for $i \in \{1,\dots,n\}$, Dirichlet characters $\varepsilon_i$ of modulus $L_i$ with values in $\mathbb{C}$, cusp forms $g_i$ of weight $k$ for $\Gamma_1(L_i)$, and cusp forms $G_{i,d}$ of weight $k$ for $\Gamma_H(M)$ indexed by $i$ and by an arbitrary natural number $d$, such that: each $g_i$ is a primitive form with character $\varepsilon_i$ in the project's sense (normalised $q$-coefficient $a_1 = 1$, the Hecke recursions at primes away from $L_i$, multiplicativity at primes dividing $L_i$, nebentypus $\varepsilon_i$, and no occurrence of the eigenpacket $(a_p(g_i), \varepsilon_i(p))$ at any proper divisor of $L_i$); for $i \ne j$ either $L_i \ne L_j$ or some $q$-expansion coefficient of $g_i$ differs from that of $g_j$; for every $u \in H$ the character $\varepsilon_i$ raised to level $M$ takes the value $1$ at $u$; for $d \mid M/L_i$ one has $G_{i,d}(\tau) = g_i(\mathrm{diag}(d,1) \cdot \tau)$ for all $\tau$ in the upper half-plane; the family $(G_{i,d})$, indexed by pairs consisting of $i$ and a divisor $d$ of $M/L_i$, is linearly independent over $\mathbb{C}$ and spans all of $S_k(\Gamma_H(M))$; and these basis elements are eigenvectors for the operators of the project (each defined by the expected slash formula when the corresponding stability predicate `StableT`, `StableD`, `StableU` holds and as the zero map otherwise), namely `heckeTLinH` at a prime $\ell \nmid M$ acts on $G_{i,d}$ by $a_\ell(g_i)$, `diamondLinH` at $u \in (\mathbb{Z}/M)^\times$ acts by $\varepsilon_i(u)$ computed at level $M$, and for a prime $q \mid M$ and $d \mid M/L_i$ the operator `heckeULinH` sends $G_{i,d}$ to $G_{i,d/q}$ if $q \mid d$, to $a_q(g_i) G_{i,d}$ if $q \nmid d$ and $q \mid L_i$, and to $a_q(g_i) G_{i,d} - \varepsilon_i(q) q^{k-1} G_{i,dq}$ if $q \nmid d$ and $q \nmid L_i$. Here $a_m(g_i)$ denotes the $m$-th coefficient of the $q$-expansion of $g_i$ with period $1$.
--
--   This is the Atkin–Lehner–Li theory of newforms and oldforms in the form needed for $\Gamma_H(M)$: the space of weight-$k$ cusp forms decomposes by nebentypus trivial on $H$ and acquires a basis of degeneracy images of finitely many pairwise distinct primitive forms, with the classical action of $T_\ell$, the diamond operators and $U_q$ on that basis. It is the source of eigenform input later in the argument: it feeds the reconstruction of an eigenform from prescribed eigenvalues, the commutation of the three families of operators, and the existence of a squarefree polynomial annihilating $T_\ell$ on the relevant cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply.lean

import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Definitions.Def_CuspForm_PrimitiveFormGamma1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CohCarrier.GammaH M H) k),
      (∀ i, CuspForm.IsPrimitiveForm (ε i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, ∀ u : (ZMod M)ˣ, u ∈ H → DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) = 1) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) = ⊤ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CuspForm.heckeTLinH k hℓ hℓM (G i d) = ModularFormClass.qCoeff (g i) ℓ • G i d) ∧
      (∀ (u : (ZMod M)ˣ) (i : Fin n) (d : ℕ), d ∣ M / L i →
        CuspForm.diamondLinH k u (G i d) = DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) • G i d) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (q ∣ d → CuspForm.heckeULinH k q (G i d) = G i (d / q)) ∧
        (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH k q (G i d) = ModularFormClass.qCoeff (g i) q • G i d) ∧
        (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH k q (G i d) =
          ModularFormClass.qCoeff (g i) q • G i d - (ε i (q : ZMod (L i)) * (q : ℂ) ^ (k - 1)) • G i (d * q))) := by sorry
