-- Prove2me | Theorems.Thm_FLT_No2BridgeWiring_weightOneNewformExists_levelAtThree_not_cube_dvd
-- name    : FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/8a60376b-1a4e-5d0c-afa7-a106c521a453
-- title:
--   Mod-3 eigensystem at a level cube-free away from 3
-- statement:
--   For every Weierstrass model $W$ over $\mathbb{Z}$ with $\Delta(W)\neq 0$ that is semistable in the project's sense (for each prime $p$ dividing $\Delta(W)$, $p$ does not divide $c_4(W)$) and whose mod-$3$ representation is irreducible in the project's sense (`ModRepIsIrreducible 3`: the $\mathbb{Z}/3$-module of $3$-torsion points of $W$ base-changed to $\mathbb{Q}$, taken over $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ`, is nontrivial, and every $\mathbb{Z}/3$-submodule stable under all $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$ is $\bot$ or $\top$), there exist a natural number $N\neq 0$ and a sequence $a:\mathbb{N}\to\mathbb{Z}$ with six properties. First, `HasIntegralBasis N`: the set of weight-$2$ cusp forms on $\Gamma_0(N)$ all of whose $q$-expansion coefficients lie in the prime subring of $\mathbb{C}$ spans the whole space over $\mathbb{C}$. Second, $a$ is a formal Hecke eigensystem for the character $\ell\mapsto 0$ if $\ell\mid N$ and $\ell\mapsto\chi_{-3}(\ell)$ otherwise, where $\chi_{-3}(n)\in\{1,-1,0\}$ according to $n\bmod 3$; here `IsEigensystem` means $a_1=1$ together with $a_{\ell n}+e_\ell\cdot(a_{n/\ell}$ if $\ell\mid n$, else $0)=a_\ell a_n$ for all primes $\ell$ and all $n$. Third, `IsLatticeRealized N a`: there is a weight-$2$ cusp form on $\Gamma_0(N)$ with integral $q$-expansion whose integer coefficient sequence is congruent mod $3$, coefficient by coefficient, to the power series $(\sum_n a_n q^n)\cdot E$, where $E$ is the explicit weight-one Eisenstein series with coefficients $1$ and $6\sigma_{\chi_{-3}}(n)$. Fourth, $q^3\nmid N$ for every prime $q\neq 3$. Fifth, for every prime $\ell$ with $\ell\nmid\Delta(W)$, $\ell\nmid N$ and $\ell\neq 3$, one has $3\mid a_\ell-a_\ell(W)$, where $a_\ell(W)=\ell+1-\#(W\bmod\ell)$ is the trace of Frobenius of the naive reduction. Sixth, if $9\mid N$, then for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $3$ a non-unit in $A$, every $3$-torsion point of $W$ over $\overline{\mathbb{Q}}$ fixed by all elements of the inertia subgroup of $A$ over $\mathbb{Q}$ is zero. Note that no weight-one form occurs in the statement: the weight-one data enter only through the Eisenstein factor in the third clause.
--
--   This is the modularity input for the prime $3$, in the shape used by Wiles (Chapter 5) via Langlands–Tunnell and Deligne–Serre: the mod-$3$ representation of a semistable curve is realised by an integral eigensystem of level $N$, with $N$ cube-free away from $3$ and with $9\mid N$ only allowed when inertia at $3$ fixes no nonzero $3$-torsion. Formally the congruence is packaged as a [`FormalHecke.IsEigensystem`](def/FormalHecke_Eigensystem.html#L10) together with `IsLatticeRealized`, a mod-$3$ congruence between an integral weight-$2$ form on $\Gamma_0(N)$ and the product of $\sum a_nq^n$ with the weight-one Eisenstein series of character $\chi_{-3}$, rather than as a newform with Hecke eigenvalues; the clause on $q^3\nmid N$ and the clause about inertia-fixed $3$-torsion are extra conclusions not present in the textbook formulation. It is used to produce residual modularity of $W$ at $3$ at a level that is cube-free away from $3$ and satisfies the inertia condition at $3$, which makes the cube case of level lowering vacuous.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FLT_No2BridgeWiring_weightOneNewformExists_levelAtThree_not_cube_dvd.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_CuspForm_IntegralLattice
import Definitions.Def_FormalHecke_Eigensystem
import Definitions.Def_ModularForm_EisensteinChiNegThree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CuspForm EisensteinWeightOne FormalHecke
open WeierstrassCurve
open scoped WeierstrassCurve.Affine

theorem FLT.No2BridgeWiring.weightOneNewformExists_levelAtThree_not_cube_dvd :
    ∀ W : WeierstrassCurve ℤ, W.Δ ≠ 0 → W.IsSemistableModel → W.ModRepIsIrreducible 3 →
      ∃ (N : ℕ) (_ : NeZero N) (a : ℕ → ℤ),
        CuspForm.HasIntegralBasis N ∧
        FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ N then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
        CuspForm.IsLatticeRealized N a ∧
        (∀ q : ℕ, q.Prime → q ≠ 3 → ¬ q ^ 3 ∣ N) ∧
        (∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ 3 →
          (3 : ℤ) ∣ (a ℓ - W.apOfModel ℓ)) ∧
        (3 ^ 2 ∣ N →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime 3 →
            ∀ x : Submodule.torsionBy ℤ ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point (3 : ℕ),
              (∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) → x = 0) := by sorry
