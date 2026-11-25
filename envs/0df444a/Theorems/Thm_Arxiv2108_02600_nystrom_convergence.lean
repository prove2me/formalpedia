-- Prove2me | Theorems.Thm_Arxiv2108_02600_nystrom_convergence
-- name    : Arxiv2108_02600.nystrom_convergence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:19:20.780718+00:00
-- url     : https://prove2.me/theorems/cdfc6997-8b20-535a-bc03-ea9b86a23c1c
-- title:
--   Theorem 4.1: convergence of the Nyström method at rate $N^{-n}$
-- statement:
--   Let $\operatorname{Re}\eta>0$, $h<c$, $c,M>0$, $n\ge1$, $f\in B^{(n)}_{c,M}$ and $\mathrm{cut}>0$. There is a constant $K$ with the following property. For every $g\in[BC^n(\mathbb R)]^2$ there is $N_0\in\mathbb N$ such that, for every $N>N_0$, the semi-discrete Nyström equation (4.2)
--
--   $$\psi_N(s)+\sum_{j\in\mathbb Z}\Big[R^{(N)}_j(s)B(s,t_j)+\frac\pi NC(s,t_j)\Big]\psi_N(t_j)=2g(s),\qquad s\in\mathbb R,\quad t_j=-\mathrm{cut}+\frac{j\pi}N,$$
--
--   has exactly one solution $\psi_N\in[BC(\mathbb R)]^2$. Moreover, every solution $\psi\in[BC(\mathbb R)]^2$ of $(I+D-i\eta S)\psi=2g$ (2.15) satisfies
--
--   $$\|\psi-\psi_N\|_{[L^\infty(\mathbb R)]^2}\le K\,N^{-n}\,\|g\|_{[BC^n(\mathbb R)]^2}.$$
--
--   This is the central result of the paper: the rate of the Nyström method is $N^{-n}$ for surfaces of class $BC^{n+2}$.
--
--   **Formalization Note** "≲" is read as a constant $K$ independent of $N$ and $g$, and $N_0$ may depend on $g$, as in the paper's wording. The equation (2.15) has exactly one bounded continuous solution by Theorem 2.2 (cited from [TA02]); the bound is stated for every such solution. $B(s,s)$ and $C(s,s)$ are the limits of $B$ and $C$ at the diagonal, not the printed values (3.15) and (3.19). The theorem prints $c>0$, and Section 2 requires $c>h$; both are hypotheses. The paper writes $n\in\mathbb N$, and the scheme is introduced for "some positive integer $n$", so $n\ge1$.
-- source:
--   J. Li, X. Liu, B. Zhang and H. Zhang, The Nyström method for elastic wave scattering by unbounded rough surfaces, arXiv:2108.02600v1 (2021), claim c010; Section 4, Theorem 4.1 with the scheme (4.2), PDF p. 14

import Mathlib
import Definitions.Def_Arxiv2108_02600_Basic

open MeasureTheory Filter Topology

namespace Arxiv2108_02600

theorem nystrom_convergence (P : Lame) (η : ℂ) (hη : 0 < η.re) (h c M : ℝ) (hhc : h < c)
    (hc : 0 < c) (hM : 0 < M) (n : ℕ) (hn : 1 ≤ n) (f : ℝ → ℝ) (hf : InB n c M f)
    (cut : ℝ) (hcut : 0 < cut) :
    ∃ K : ℝ, ∀ g : ℝ → Fin 2 → ℂ, IsBCn n g → ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∃ psiN : ℝ → Fin 2 → ℂ, IsBC psiN ∧ SolvesNystrom P η h f cut N g psiN ∧
        (∀ phi : ℝ → Fin 2 → ℂ, IsBC phi → SolvesNystrom P η h f cut N g phi → phi = psiN) ∧
        ∀ psi : ℝ → Fin 2 → ℂ, IsBC psi → SolvesBIE P η h f g psi →
          ∀ s : ℝ, ‖psi s - psiN s‖ ≤ K * (N : ℝ) ^ (-(n : ℝ)) * bcnNorm n g := by sorry

end Arxiv2108_02600
