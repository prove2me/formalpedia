-- Prove2me | Theorems.Thm_Arxiv2610_39302_bad_views_capture_nuisance
-- name    : Arxiv2610_39302.bad_views_capture_nuisance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:03:45.218661+00:00
-- url     : https://prove2.me/theorems/5ee5f6ad-8cc7-5818-a19b-d0e4445c923c
-- title:
--   Proposition 3 (ii): bad views capture nuisance
-- statement:
--   Let $Z$ be a finite world with $p>0$, let a modality observe state $z$ with a nuisance $\nu\sim q$ on a finite set $N$, $q>0$, independent of $z$, and let a bad-view JEPA corrupt state and nuisance independently: $\Gamma=A\otimes B$, with $A$ and $B$ row-stochastic with stationary laws $p$ and $q$. Its positive pairs are two corruptions of one observation, drawn independently given it. Let $1=\alpha_0\ge\alpha_1\ge\cdots$ and $1=\beta_0\ge\beta_1\ge\cdots$ be the eigenvalues of $A^*A$ on $L^2(p)$ and $B^*B$ on $L^2(q)$ ($\alpha_i:=-\infty$ for $i\ge|Z|$), let $\xi_1\ge\xi_2\ge\cdots$ be the products $\alpha_i\beta_j$ with $(i,j)\ne(0,0)$, with multiplicity, take the objective of Proposition 1 with $1\le k<|Z||N|$, and suppose $\xi_k>\xi_{k+1}$. Let $r$ be the number of the top $k$ pairs $(i,j)$ that have $j\ge1$. Then:
--
--   1. the kernel of the bad-view JEPA has eigenvalues $\alpha_i\beta_j$, with multiplicity, and eigenfunctions $\psi_i(z)\chi_j(\nu)$ for eigenfunctions $\psi_i$ of $A^*A$ and $\chi_j$ of $B^*B$;
--   2. every minimiser $f$ has $C_f$ with exactly $r$ zero eigenvalues, and $\rho(f)=1-r/k$;
--   3. for every centred, whitened encoder $f_2$ of another modality with nuisance law $q_2>0$, and every $Q\in O(k)$, the alignment error over paired observations with independent nuisances satisfies
--   $$E\,\|Qf(x_1)-f_2(x_2)\|^2\ge2r;$$
--   4. $r\ge1$ if and only if $\beta_1>\alpha_k$.
--
--   **Formalization Note** "$r$ of the top $k$" is the number of pairs $(i,j)$ with $j\ge1$ and $\alpha_i\beta_j\ge\xi_k$; under the separation $\xi_k>\xi_{k+1}$ exactly $k$ pairs have $\alpha_i\beta_j\ge\xi_k$. When $k+1>|Z||N|-1$ there is no $\xi_{k+1}$ and the separation hypothesis is read as empty ($\xi_{k+1}:=-\infty$). In item 4, $\beta_1$ exists only when $|N|\ge2$; for $|N|=1$ it is read as $-\infty$, and $\alpha_k=-\infty$ when $k\ge|Z|$. Item 1 is stated as equality of the eigenvalue multiset of $K$ with the multiset of products, and as the eigenfunction relation for the Markov operators. Encoders are written as functions of state and nuisance.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c009; Section 2.3, Proposition 3 (ii), PDF p. 5; formal statement and proof in Appendix A.4, PDF p. 21

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem bad_views_capture_nuisance {Z N₁ N₂ : Type*} [Fintype Z] [DecidableEq Z]
    [Fintype N₁] [DecidableEq N₁] [Fintype N₂] {k : ℕ}
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (q₁ : N₁ → ℝ) (hq₁ : ∀ ν, 0 < q₁ ν) (hq₁1 : ∑ ν, q₁ ν = 1)
    (A : Matrix Z Z ℝ) (hA : IsStationaryStochastic p A)
    (B : Matrix N₁ N₁ ℝ) (hB : IsStationaryStochastic q₁ B)
    (hk : 1 ≤ k) (hkX : k < Fintype.card Z * Fintype.card N₁)
    (hsep : k + 2 ≤ Fintype.card Z * Fintype.card N₁ → xi p q₁ A B (k + 1) < xi p q₁ A B k) :
    (kerMat (prodLaw p q₁) (badViewLaw p q₁ A B)).charpoly.roots =
      (Finset.range (Fintype.card Z) ×ˢ Finset.range (Fintype.card N₁)).val.map
        (badEig p q₁ A B) ∧
    (∀ (ψ : Z → ℝ) (χ : N₁ → ℝ) (a b : ℝ),
      (markovOp p (twoCorruptLaw p A)).mulVec ψ = a • ψ →
      (markovOp q₁ (twoCorruptLaw q₁ B)).mulVec χ = b • χ →
      (markovOp (prodLaw p q₁) (badViewLaw p q₁ A B)).mulVec (fun x => ψ x.1 * χ x.2) =
        (a * b) • (fun x => ψ x.1 * χ x.2)) ∧
    (∀ f : Z × N₁ → Fin k → ℝ,
      (∀ f' : Z × N₁ → Fin k → ℝ, spectralLoss (prodLaw p q₁) (badViewLaw p q₁ A B) f ≤
        spectralLoss (prodLaw p q₁) (badViewLaw p q₁ A B) f') →
      (stateCov (prodLaw p q₁) Prod.fst f).charpoly.roots.count 0 = nuisanceCount p q₁ A B k ∧
      rho (prodLaw p q₁) Prod.fst f = 1 - (nuisanceCount p q₁ A B k : ℝ) / k ∧
      ∀ (q₂ : N₂ → ℝ), (∀ ν, 0 < q₂ ν) → ∑ ν, q₂ ν = 1 →
        ∀ e₂ : Z × N₂ → Fin k → ℝ, IsWhitened (prodLaw p q₂) e₂ →
          ∀ Q : Matrix.orthogonalGroup (Fin k) ℝ,
            2 * (nuisanceCount p q₁ A B k : ℝ) ≤
              ∑ z, ∑ ν₁, ∑ ν₂, p z * q₁ ν₁ * q₂ ν₂ * sqNorm (rot Q (f (z, ν₁)) - e₂ (z, ν₂))) ∧
    (1 ≤ nuisanceCount p q₁ A B k ↔
      2 ≤ Fintype.card N₁ ∧ (k < Fintype.card Z → corrEig p A k < corrEig q₁ B 1)) := by sorry

end Arxiv2610_39302
