-- Prove2me | Theorems.Thm_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast
-- name    : CuspForm.exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:38.373155+00:00
-- url     : https://prove2.me/theorems/15c410aa-1e82-51a1-bd0a-394a960f66fa
-- title:
--   A basis of S₂(Γ₀(N)) with rational Hecke matrices
-- statement:
--   Let $N$ be a natural number, assumed nonzero. The assertion is that there exist a natural number $n$ and a basis $b : \mathrm{Fin}\ n \to S_2(\Gamma_0(N))$ of the complex vector space of weight-two cusp forms for the congruence subgroup $\Gamma_0(N)$, such that two families of rationality statements hold simultaneously. First, for every natural number $\ell$ that is prime and does not divide $N$, and all indices $i, j \in \mathrm{Fin}\ n$, the $j$-th coordinate with respect to $b$ of [`CuspForm.heckeTLin 2 hℓ hℓN (b i)`](def/ModularForm_HeckeOperatorForms.html#L69) lies in the image of the inclusion $\mathbb{Q} \to \mathbb{C}$; here `heckeTLin` is the $\mathbb{C}$-linear endomorphism of $S_2(\Gamma_0(N))$ sending a cusp form $f$ to the cusp form whose underlying function is $\sum_{j < \ell} f \mid_2 \mathrm{heckeMatrix}\ \ell\ j + f \mid_2 \mathrm{heckeDiagMatrix}\ \ell$, a sum of weight-two slash actions by the matrices `heckeMatrix` and `heckeDiagMatrix`. Second, for every prime $q$ dividing $N$ and all $i, j$, the $j$-th coordinate of [`CuspForm.heckeULin 2 hqN (b i)`](def/ModularForm_HeckeOperatorForms.html#L83) is likewise rational, `heckeULin` being the endomorphism given on underlying functions by $f \mapsto \sum_{j < q} f \mid_2 \mathrm{heckeMatrix}\ q\ j$. Thus one single basis makes the matrices of all the operators $T_\ell$ ($\ell \nmid N$) and $U_q$ ($q \mid N$) have rational entries.
--
--   This is the rational structure of the space of weight-two cusp forms on $\Gamma_0(N)$: classically, $S_2(\Gamma_0(N))$ is spanned by forms with rational Fourier coefficients, and the Hecke operators preserve rationality of $q$-expansions, so all Hecke matrices can be made rational at once. It is used in the comparison of the Hecke action on cusp forms with the Hecke action on the rational Tate module and the period lattice of the modular curve, and in the finiteness statement for kernels of Hecke generators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem CuspForm.exists_basis_repr_heckeTLin_heckeULin_mem_range_ratCast (N : ℕ) [NeZero N] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)),
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i j : Fin n),
          b.repr (CuspForm.heckeTLin 2 hℓ hℓN (b i)) j ∈ Set.range ((↑) : ℚ → ℂ)) ∧
        (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (i j : Fin n),
          b.repr (CuspForm.heckeULin 2 hqN (b i)) j ∈ Set.range ((↑) : ℚ → ℂ)) := by sorry
