-- Prove2me | Theorems.Thm_Arxiv2610_39302_nuisance_costs_alignment
-- name    : Arxiv2610_39302.nuisance_costs_alignment
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:02:47.766346+00:00
-- url     : https://prove2.me/theorems/246aed71-7433-585b-a9c3-a2bcd3213bb5
-- title:
--   Theorem 3: nuisance costs alignment
-- statement:
--   Let $Z$ be a finite world with $p(z)>0$, $\sum_zp(z)=1$. For $m=1,2$ let modality $m$ observe state $z$ with a nuisance $\nu\sim q_m$ on a finite set $N_m$, $q_m(\nu)>0$, independent of $z$, and let $f_m$ be an encoder into $\mathbb{R}^k$, $k\ge1$, written $e_m(z,\nu)=f_m(g_m(z,\nu))$, that is centred and whitened on its observations. Over paired observations $x_1=g_1(z,\nu_1)$, $x_2=g_2(z,\nu_2)$ of one state with independent nuisances, for every $Q\in O(k)$,
--
--   $$E\,\|Qf_1(x_1)-f_2(x_2)\|^2\ge2k\Big(1-\min_m\rho(f_m)\Big),$$
--
--   and $\rho(f_m)=1$ if and only if $f_m(x)$ is a function of the world state alone.
--
--   Every direction an encoder spends on its own nuisance is lost for alignment, whatever whitened embedding the other modality learns.
--
--   **Formalization Note** Encoders on observations $g_m(z,\nu)$ (with $g_m$ injective) are written as functions $e_m$ of state and nuisance. The nuisance sets are finite, as in the model of Appendix A.4. "$\min_Q\ge$" is stated for every $Q$. Since all probabilities are positive, "a function of the state alone" means $e_m(z,\nu)=e_m(z,\nu')$ for all $z,\nu,\nu'$.
-- source:
--   Balestriero and LeCun, Proving and Improving the Platonic Representation Hypothesis with JEPAs, arXiv:2610.39302v1 (2026), claim c062; Section 2.3, Theorem 3, eq. (4), PDF p. 5; proof in Appendix A.4, PDF p. 21

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open MeasureTheory Filter Topology Matrix

namespace Arxiv2610_39302

theorem nuisance_costs_alignment {Z N₁ N₂ : Type*} [Fintype Z] [DecidableEq Z] [Fintype N₁]
    [Fintype N₂] {k : ℕ} (hk : 1 ≤ k)
    (p : Z → ℝ) (hp : ∀ z, 0 < p z) (hp1 : ∑ z, p z = 1)
    (q₁ : N₁ → ℝ) (hq₁ : ∀ ν, 0 < q₁ ν) (hq₁1 : ∑ ν, q₁ ν = 1)
    (q₂ : N₂ → ℝ) (hq₂ : ∀ ν, 0 < q₂ ν) (hq₂1 : ∑ ν, q₂ ν = 1)
    (e₁ : Z × N₁ → Fin k → ℝ) (e₂ : Z × N₂ → Fin k → ℝ)
    (he₁ : IsWhitened (prodLaw p q₁) e₁) (he₂ : IsWhitened (prodLaw p q₂) e₂) :
    (∀ Q : Matrix.orthogonalGroup (Fin k) ℝ,
      2 * k * (1 - min (rho (prodLaw p q₁) Prod.fst e₁) (rho (prodLaw p q₂) Prod.fst e₂)) ≤
        ∑ z, ∑ ν₁, ∑ ν₂, p z * q₁ ν₁ * q₂ ν₂ * sqNorm (rot Q (e₁ (z, ν₁)) - e₂ (z, ν₂))) ∧
    (rho (prodLaw p q₁) Prod.fst e₁ = 1 ↔ ∀ z ν ν', e₁ (z, ν) = e₁ (z, ν')) ∧
    (rho (prodLaw p q₂) Prod.fst e₂ = 1 ↔ ∀ z ν ν', e₂ (z, ν) = e₂ (z, ν')) := by sorry

end Arxiv2610_39302
