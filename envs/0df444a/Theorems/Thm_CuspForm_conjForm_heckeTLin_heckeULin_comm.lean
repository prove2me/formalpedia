-- Prove2me | Theorems.Thm_CuspForm_conjForm_heckeTLin_heckeULin_comm
-- name    : CuspForm.conjForm_heckeTLin_heckeULin_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.686216+00:00
-- url     : https://prove2.me/theorems/681f6628-d0f8-5bc6-9cb6-37c364610882
-- title:
--   Conjugation of cusp forms commutes with all Hecke operators
-- statement:
--   Let $N$ be a nonzero natural number and $k$ an integer, and let $\rho$ be any self-map of the space $S_k(\Gamma_0(N))$ of cusp forms of weight $k$ for $\Gamma_0(N)$ which is given pointwise by conjugation: for every cusp form $f$ and every $\tau$ in the upper half-plane, $(\rho f)(\tau) = \overline{f(-\overline{\tau})}$, the point $-\overline{\tau}$ again lying in the upper half-plane since its imaginary part is that of $\tau$. (No linearity, continuity or other structural property of $\rho$ is assumed; only this formula.) The assertion is the conjunction of two commutation statements. First, for every prime $\ell$ with $\ell \nmid N$ and every $f \in S_k(\Gamma_0(N))$, $\rho(T_\ell f) = T_\ell(\rho f)$, where [`CuspForm.heckeTLin`](def/ModularForm_HeckeOperatorForms.html#L69) is the $\mathbb{C}$-linear operator whose underlying function is $\mathrm{heckeT}\,k\,\ell\,f = \sum_{j<\ell} f \mid_k \mathrm{heckeMatrix}\,\ell\,j + f\mid_k \mathrm{heckeDiagMatrix}\,\ell$, a sum of weight-$k$ slashes. Second, for every natural number $q$ dividing $N$ — not assumed prime — and every $f$, $\rho(U_q f) = U_q(\rho f)$, where [`CuspForm.heckeULin`](def/ModularForm_HeckeOperatorForms.html#L83) has underlying function $\mathrm{heckeU}\,k\,q\,f = \sum_{j<q} f\mid_k \mathrm{heckeMatrix}\,q\,j$.
--
--   This expresses the reality of the Hecke operators $T_\ell$ ($\ell \nmid N$) and $U_q$ ($q \mid N$) on $S_k(\Gamma_0(N))$: they are defined by coset sums with rational matrices, hence commute with the conjugation involution $f \mapsto \overline{f(-\overline{\,\cdot\,})}$, which is the slash by $\mathrm{diag}(-1,1)$. It is used in the construction of an integral (in particular conjugation-stable) structure on spaces of cusp forms, via [`CuspForm.hasIntegralStructure_of_two_le`](thm.html#CuspForm.hasIntegralStructure_of_two_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspForm_conjForm_heckeTLin_heckeULin_comm.lean

import Definitions.Def_ModularForm_HeckeOperatorForms

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CuspForm.conjForm_heckeTLin_heckeULin_comm (N : ℕ) [NeZero N] (k : ℤ)
    (ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k → CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hρ : ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane),
      ρ f τ = (starRingEnd ℂ) (f ⟨-((starRingEnd ℂ) (τ : ℂ)), by simpa using τ.im_pos⟩)) :
    (∀ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k),
        ρ (CuspForm.heckeTLin k hℓ hℓN f) = CuspForm.heckeTLin k hℓ hℓN (ρ f)) ∧
      (∀ {q : ℕ} (hqN : q ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k),
        ρ (CuspForm.heckeULin k hqN f) = CuspForm.heckeULin k hqN (ρ f)) := by sorry
