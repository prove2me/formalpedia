-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_lower_bound_step_two_truncated
-- name    : BanditAlgorithm.mdp_lower_bound_step_two_truncated
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-04T04:13:18.933733+00:00
-- url     : https://prove2.me/theorems/4218abf4-00e0-4a25-9522-5dfc681f2628
-- title:
--   Step 2 of the MDP minimax lower bound, with truncated counts
-- statement:
--   Step 2 of the proof of the $\Omega(\sqrt{DSAn})$ minimax regret lower bound for average-reward Markov decision processes (Lattimore--Szepesv\'ari, *Bandit Algorithms*, Theorem 38.7), in the form the truncated visit counts actually supply.
--
--   Here $V^t_j=\mathbb E_0[T_j]$ are the **truncated** per-pair counts — visits to the $j$-th leaf--action pair among the first $N$ leaf visits — with total $T_0=\mathbb E_0[T_\sigma]$, bounded below by Claim 38.10 in its truncated form; $V_j=\mathbb E_0[T_j^{\mathrm{full}}]$ are the **full** counts, which is what the divergence decomposition (eq. 38.22) produces, and only their total $T_0^{\mathrm{full}}$ needs an upper bound.  The parameter $\mathrm{cap}$ is the pathwise bound on the observable $T_\sigma-T_j$ and enters the Pinsker penalty as $\mathrm{cap}\cdot\Delta$.
--
--   Under Claim 38.10 in the two-sided form $c_1n/D\le T_0$, $T_0^{\mathrm{full}}\le c_2n/D$, the change-of-measure bound, Claim 38.11 in the form $R_j\ge c_3\Delta D\,W_j-\mathrm{slack}$, and the tuning $\Delta=\frac{c_1(k-1)}{2}\sqrt{D/(2c_2nk)}$, some alternative $j$ satisfies
--   $$R_j\;\ge\;\frac{c_1^2c_3}{16}\sqrt{\frac{Dkn}{2c_2}}-\mathrm{slack}.$$
--
--   Compared with the single-total form, the roles of $c_1$ and $c_2$ have separated — $c_1$ bounds the truncated total below, $c_2$ bounds the full total above — so the two constants need no relation to each other.  The parameter $D$ is a free scale, not necessarily the diameter.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), https://tor-lattimore.com/downloads/book/book.pdf, section 38.7, eq. (38.24) and the two displays following it (printed p. 531, PDF p. 540); Theorem 38.7 (printed p. 523).

import Mathlib.Data.Real.Sqrt

open Finset

theorem BanditAlgorithm.mdp_lower_bound_step_two_truncated
    {ι : Type*} [Fintype ι] {k : ℕ} (hk : 2 ≤ k) (hcard : Fintype.card ι = k)
    (n D cap c₁ c₂ c₃ Δ T0 T0full slack : ℝ)
    (V Vt W R : ι → ℝ)
    (hn : 0 < n) (hD : 0 < D) (hcap0 : 0 ≤ cap) (hcap : cap ≤ n / D)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hV : ∀ j, 0 ≤ V j) (hsumV : ∑ j, V j = T0full) (hsumVt : ∑ j, Vt j = T0)
    (hT0lo : c₁ * n / D ≤ T0) (hfullhi : T0full ≤ c₂ * n / D)
    (hΔ : Δ = c₁ * ((k : ℝ) - 1) / 2 * Real.sqrt (D / (2 * c₂ * n * k)))
    (hW : ∀ j, T0 - Vt j - cap * Δ * Real.sqrt (2 * V j) ≤ W j)
    (hR : ∀ j, c₃ * Δ * D * W j - slack ≤ R j) :
    ∃ j : ι,
      c₁ ^ 2 * c₃ / 16 * Real.sqrt (D * k * n / (2 * c₂)) - slack ≤ R j := by sorry
