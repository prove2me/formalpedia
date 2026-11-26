-- Prove2me | Theorems.Thm_CondMat0408017_leakage_suppression
-- name    : CondMat0408017.leakage_suppression
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-26T13:24:16.164947+00:00
-- url     : https://prove2.me/theorems/4e1249fd-7239-5112-b17d-5c645ab0155c
-- title:
--   Eqs. (139)-(140): a West-O'Donnell spectrum keeps the SPP out of the radiative region for $n$ scattering events if $\Delta k<(k_1-\omega/c)/n$
-- statement:
--   Let $k_1>0$ be the real part of the wave number of an incident SPP and $\Delta k\ge0$. Let each interaction with the roughness transfer a momentum $Q$ in the support of the West-O'Donnell power spectrum (139), $2k_1-\Delta k\le|Q|\le2k_1+\Delta k$. After $j$ interactions with transfers $Q_1,\dots,Q_j$:
--
--   1. the wave number $k_1+\sum_iQ_i$ lies within $j\Delta k$ of $(2s+1)k_1$ for some integer $s$ with $|s|\le j$ and $s\equiv j\pmod 2$. For $j=1,2,3$ these are the paper's intervals around $3k_1,-k_1$; $5k_1,k_1,-3k_1$; $7k_1,3k_1,-k_1,-5k_1$;
--   2. if $n\ge j$, $\omega/c\ge0$ and $\Delta k<(k_1-\omega/c)/n$, then $|k_1+\sum_iQ_i|>\omega/c$: the SPP has not been converted into volume waves ($|q|\le\omega/c$) within $n$ scattering events.
--
--   **Formalization Note** As in the paper's argument, only real parts of wave numbers are tracked, and each event adds a momentum from the support of $g$. The support is taken closed, which allows more transfers than the open intervals of (139). The text says the spectrum is located around $\pm k_1$, but (139) with $k_\pm=2k_1\pm\Delta k$ puts it around $\pm2k_1$, which the argument needs. The formula is followed.
-- source:
--   I. Simonsen, A random walk through surface scattering phenomena: Theory and phenomenology, arXiv:cond-mat/0408017v1 (2004), claim c044; Sec. IV.B.2, eq. (Eq:Loc:power) [(139)] and the argument after it, PDF pp. 48-49

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex

namespace CondMat0408017

theorem leakage_suppression (k1 Δk : ℝ) (hk1 : 0 < k1) (hΔk : 0 ≤ Δk) :
    ∀ (j : ℕ) (Q : Fin j → ℝ), (∀ i, Q i ∈ westODonnellSupport k1 Δk) →
      (∃ s : ℤ, |s| ≤ (j : ℤ) ∧ Even (s + (j : ℤ)) ∧
        |k1 + ∑ i, Q i - (2 * (s : ℝ) + 1) * k1| ≤ (j : ℝ) * Δk) ∧
      ∀ (n : ℕ) (wv : ℝ), 0 ≤ wv → j ≤ n → Δk < (k1 - wv) / n → wv < |k1 + ∑ i, Q i| := by sorry

end CondMat0408017
