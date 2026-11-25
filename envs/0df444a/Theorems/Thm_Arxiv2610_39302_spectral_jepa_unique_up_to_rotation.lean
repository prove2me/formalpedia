-- Prove2me | Theorems.Thm_Arxiv2610_39302_spectral_jepa_unique_up_to_rotation
-- name    : Arxiv2610_39302.spectral_jepa_unique_up_to_rotation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:00:40.253346+00:00
-- url     : https://prove2.me/theorems/02efbfa9-9fbd-4560-921e-e91b31ca725c
-- title:
--   Proposition 1: spectral JEPAs are unique up to rotation
-- statement:
--   Let $Z$ be a finite world with $p(z)>0$, let $\pi$ be a positive-pair law with marginals $p$, let $\ell(a,b)=\|a-b\|^2$, let $\Omega$ whiten the embeddings ($E_ph=0$, $E_phh^\top=I_k$, as a hard constraint), and let $1\le k<|Z|$. Then:
--
--   1. the minimum of the objective is
--   $$\min L_\pi=2\sum_{i=1}^k(1-\mu_i),$$
--   and it is attained;
--   2. a spectral embedding $\Phi_\pi(z)=(v_1(z),\dots,v_k(z))/\sqrt{p(z)}$ exists;
--   3. if $\mu_k>\mu_{k+1}$ (with $\mu_{|Z|}:=-\infty$), then for every spectral embedding $\Phi_\pi$ the minimisers of $L_\pi$ are exactly the embeddings $Q\Phi_\pi$, $Q\in O(k)$.
--
--   Under the gap, this supplies the uniqueness hypothesis of Theorem 1.
--
--   **Formalization Note** "$\min L_\pi=c$" is stated as: $c$ is the least value of $L_\pi$ over all embeddings $h:Z\to\mathbb{R}^k$. The convention $\mu_{|Z|}=-\infty$ makes the gap hypothesis empty when $k+1=|Z|$.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c003; Section 2.1, Proposition 1, PDF p. 3; proof in Appendix A.2, PDF p. 20

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem spectral_jepa_unique_up_to_rotation {Z : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π) (hk : 1 ≤ k) (hkZ : k < Fintype.card Z) :
    IsLeast (Set.range (spectralLoss (k := k) p π))
      ((2 * ∑ i ∈ Finset.Icc 1 k, (1 - eigs p π i) : ℝ) : EReal) ∧
    (∃ Phi : Z → Fin k → ℝ, IsSpectralEmbedding p π Phi) ∧
    ((k + 1 < Fintype.card Z → eigs p π (k + 1) < eigs p π k) →
      ∀ Phi : Z → Fin k → ℝ, IsSpectralEmbedding p π Phi →
        ∀ h : Z → Fin k → ℝ, (∀ h' : Z → Fin k → ℝ, spectralLoss p π h ≤ spectralLoss p π h') ↔
          ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z, h z = rot Q (Phi z)) := by sorry

end Arxiv2610_39302
