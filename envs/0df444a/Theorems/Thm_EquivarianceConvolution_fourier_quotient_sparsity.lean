-- Prove2me | Theorems.Thm_EquivarianceConvolution_fourier_quotient_sparsity
-- name    : EquivarianceConvolution.fourier_quotient_sparsity
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:59:39.769166+00:00
-- url     : https://prove2.me/theorems/6fde41f0-ac4a-41c0-aed4-e4a3256f0a63
-- title:
--   Proposition 1: sparsity of Fourier transforms of functions on quotient spaces
-- statement:
--   Let $G$ be a finite group, $H\le G$ a subgroup and $\rho$ an irreducible representation of $G$. Assume that, on restriction to $H$, $\rho$ decomposes into irreps of $H$ as $\rho|_H=\mu_1\oplus\cdots\oplus\mu_k$ (block diagonal with consecutive blocks). Then:
--
--   1. If $f:G/H\to\mathbb C$, the column $[\hat f(\rho)]_{*,j}$ is zero unless the block of $\rho|_H$ at column $j$ is the trivial representation of $H$.
--   2. If $f:H\backslash G\to\mathbb C$, the row $[\hat f(\rho)]_{i,*}$ is zero unless the block of $\rho|_H$ at row $i$ is the trivial representation of $H$.
--   3. If $K\le G$ is a further subgroup with $\rho|_K=\nu_1\oplus\cdots\oplus\nu_{k'}$ in the same basis, and $f:H\backslash G/K\to\mathbb C$, then
--
--   $$[\hat f(\rho)]_{i,j}=0$$
--
--   unless the block of $\rho|_H$ at row $i$ is trivial **and** the block of $\rho|_K$ at column $j$ is trivial.
--
--   Here $\hat f(\rho)=\sum_{u\in G}f\uparrow^G(u)\rho(u)$. The proposition explains why Fourier transforms of functions on quotient spaces have as many matrix entries as those of functions on $G$: the extra entries are forced to vanish.
--
--   **Formalization Note** In part 3 the function on $H\backslash G/K$ is given by its lift, a function on $G$ that is left $H$-invariant and right $K$-invariant. A block is trivial when it is $1\times1$ and equal to $1$ on the subgroup.
-- source:
--   Kondor and Trivedi, On the Generalization of Equivariance and Convolution in Neural Networks to the Action of Compact Groups, arXiv:1802.03690v3 (ICML 2018), Section 4.2, Proposition 1, p. 6; proof in Appendix C, pp. 11-12

import Mathlib
import Definitions.Def_EquivarianceConvolution_Basic

open scoped BigOperators

namespace EquivarianceConvolution

theorem fourier_quotient_sparsity {G : Type*} [Group G] [Fintype G] {n : ℕ}
    (ρ : G →* Matrix (Fin n) (Fin n) ℂ) (hρ : IsIrrep ρ) (H : Subgroup G) {k : ℕ}
    (bH : Fin n → Fin k) (hbH : IsRestrictionDecomp H ρ bH) :
    (∀ (f : G ⧸ H → ℂ) (i j : Fin n), ¬ IsTrivialBlock H ρ bH (bH j) →
      groupFourier ρ (liftQ f) i j = 0) ∧
    (∀ (f : Quotient (QuotientGroup.rightRel H) → ℂ) (i j : Fin n),
      ¬ IsTrivialBlock H ρ bH (bH i) → groupFourier ρ (liftR f) i j = 0) ∧
    (∀ (K : Subgroup G) (k' : ℕ) (bK : Fin n → Fin k'), IsRestrictionDecomp K ρ bK →
      ∀ (f : G → ℂ), IsDoubleCosetFun H K f → ∀ i j : Fin n,
        (¬ IsTrivialBlock H ρ bH (bH i) ∨ ¬ IsTrivialBlock K ρ bK (bK j)) →
          groupFourier ρ f i j = 0) := by sorry

end EquivarianceConvolution
