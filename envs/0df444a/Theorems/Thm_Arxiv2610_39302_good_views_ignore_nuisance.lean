-- Prove2me | Theorems.Thm_Arxiv2610_39302_good_views_ignore_nuisance
-- name    : Arxiv2610_39302.good_views_ignore_nuisance
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:03:16.54901+00:00
-- url     : https://prove2.me/theorems/72830a6b-b9b7-5b02-89b7-c82529f53481
-- title:
--   Proposition 3 (i): good views ignore nuisance
-- statement:
--   Let $Z$ be a finite world with $p>0$, $\pi$ a positive-pair law with marginals $p$, and $1\le k<|Z|$. Let any number of modalities $m$ each observe state $z$ with a nuisance $\nu\sim q_m$ on a finite set $N_m$, $q_m>0$, independent of $z$. A good-view JEPA of modality $m$ takes the objective of Proposition 1 on observations $(z,\nu)$, with law $p(z)q_m(\nu)$, and positive pairs of law $\pi(z,z')q_m(\nu)q_m(\nu')$ (kernel $\Pi\otimes q_mq_m^\top$). If
--
--   $$\mu_k>\max(\mu_{k+1},0)\qquad(\mu_{|Z|}:=-\infty),$$
--
--   then:
--
--   1. a spectral embedding $\Phi_\pi$ exists, and for every spectral embedding $\Phi_\pi$ the minimisers of each modality's good-view objective are exactly the encoders $e(z,\nu)=Q\Phi_\pi(z)$, $Q\in O(k)$;
--   2. every minimiser is a function of the state alone: $\rho=1$;
--   3. good-view JEPAs of any two modalities agree up to one rotation on every observation: $e_m(z,\nu)=Q\,e_{m'}(z,\nu')$ for all $z,\nu,\nu'$, for some $Q\in O(k)$.
--
--   **Formalization Note** Encoders on observations are written as functions of state and nuisance. The good-view positive-pair law is the definition of $\Pi\otimes q_mq_m^\top$.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c009; Section 2.3, Proposition 3 (i), PDF p. 5; formal statement and proof in Appendix A.4, PDF p. 21

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem good_views_ignore_nuisance {Z ι : Type*} [Fintype Z] [DecidableEq Z] {k : ℕ}
    (N : ι → Type*) [∀ m, Fintype (N m)] [∀ m, DecidableEq (N m)]
    (p : Z → ℝ) (π : Z → Z → ℝ) (hπ : IsPairLaw p π) (hk : 1 ≤ k) (hkZ : k < Fintype.card Z)
    (q : ∀ m, N m → ℝ) (hq : ∀ m ν, 0 < q m ν) (hq1 : ∀ m, ∑ ν, q m ν = 1)
    (hpos : 0 < eigs p π k) (hgap : k + 1 < Fintype.card Z → eigs p π (k + 1) < eigs p π k) :
    (∃ Phi : Z → Fin k → ℝ, IsSpectralEmbedding p π Phi) ∧
    (∀ Phi : Z → Fin k → ℝ, IsSpectralEmbedding p π Phi →
      ∀ m (e : Z × N m → Fin k → ℝ),
        (∀ e' : Z × N m → Fin k → ℝ, spectralLoss (prodLaw p (q m)) (goodViewLaw π (q m)) e ≤
          spectralLoss (prodLaw p (q m)) (goodViewLaw π (q m)) e') ↔
        ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z ν, e (z, ν) = rot Q (Phi z)) ∧
    (∀ m (e : Z × N m → Fin k → ℝ),
      (∀ e' : Z × N m → Fin k → ℝ, spectralLoss (prodLaw p (q m)) (goodViewLaw π (q m)) e ≤
        spectralLoss (prodLaw p (q m)) (goodViewLaw π (q m)) e') →
      rho (prodLaw p (q m)) Prod.fst e = 1) ∧
    (∀ m m' (e : Z × N m → Fin k → ℝ) (e' : Z × N m' → Fin k → ℝ),
      (∀ e'' : Z × N m → Fin k → ℝ, spectralLoss (prodLaw p (q m)) (goodViewLaw π (q m)) e ≤
        spectralLoss (prodLaw p (q m)) (goodViewLaw π (q m)) e'') →
      (∀ e'' : Z × N m' → Fin k → ℝ, spectralLoss (prodLaw p (q m')) (goodViewLaw π (q m')) e' ≤
        spectralLoss (prodLaw p (q m')) (goodViewLaw π (q m')) e'') →
      ∃ Q : Matrix.orthogonalGroup (Fin k) ℝ, ∀ z ν ν', e (z, ν) = rot Q (e' (z, ν'))) := by sorry

end Arxiv2610_39302
