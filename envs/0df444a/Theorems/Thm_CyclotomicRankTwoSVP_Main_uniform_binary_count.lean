-- Prove2me | Theorems.Thm_CyclotomicRankTwoSVP_Main_uniform_binary_count
-- name    : CyclotomicRankTwoSVP.Main.uniform_binary_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:00.494366+00:00
-- url     : https://prove2.me/theorems/cc2d9bdf-2cab-4389-9110-29f05944d642
-- title:
--   Theorem 3.4 — uniform fixed-coordinate binary count
-- statement:
--   There are sufficiently large absolute positive integers $C_0,k_0$ and an absolute $c>0$, chosen before all parameters below. For every $k\ge k_0$, odd prime $q\ge(2k)^{C_0}$, compatible syndrome $u$, position set $P\subseteq\mathbb F_q$ with $|P|\le\sqrt{k}$, and Boolean assignment $\eta$ on $P$, put $t=\sum_{a\in P}\eta_a$. With $h=\lfloor21k/20\rfloor$,
--
--   $$\left|\frac{(h-t)!\,|F(u;P,\eta)|}{q^{h-t-k+1}}-1\right|\le q^{-ck}+\frac{3k^2}{q}<\frac14.$$
--
--   Moreover, for every $\varepsilon>0$ there is an absolute $K_0\ge k_0$ such that this same error majorant is less than $\varepsilon$ for every $k\ge K_0$ and allowed $q$. Consequently $|F|=(1+o(1))q^{h-t-k+1}/(h-t)!$ uniformly in all $q,u,P,\eta$. This states both the quantitative relative error and the uniform asymptotic, not only nonemptiness.
--
--   Differences from the source:
--   - encoding: one sufficiently large absolute pair C_0,k_0 → existential positive integer thresholds before every k,q and every instance; reason: taking maxima of the finitely many threshold witnesses supplies one common pair; increasing either threshold preserves each domain-restricted conclusion
--   - encoding: indices [r] = {1,...,r} and field elements F_q → Fin r and ZMod q; beta uses the row index plus one; reason: finite reindexing changes no instance or ordered pair
--   - encoding: q^{-Omega(k)} and uniform o(1) → one positive absolute exponent c and the explicit epsilon-threshold quantification for its majorant; reason: the uniform exponential bound and convergence have the full printed dependencies
-- source:
--   Jiaqi Liu, Yansong Feng, Yanbin Pan, SVP Is NP-Hard for Some Rank-2 Cyclotomic Modules, STOC 2027 submission #1423 (October 2026), printed p. 11 / PDF p. 12, Theorem 3.4

import Mathlib
import Definitions.Def_CyclotomicRankTwoSVP_Main_Counting

namespace CyclotomicRankTwoSVP.Main
open scoped BigOperators

theorem uniform_binary_count :
    ∃ (C₀ k₀ : ℕ) (c : ℝ), 1 ≤ C₀ ∧ 1 ≤ k₀ ∧ 0 < c ∧
      (∀ (k q : ℕ) [Fact q.Prime], Odd q → parameterDomain C₀ k₀ k q →
        ∀ (u : Fin k → ZMod q) (P : Finset (ZMod q)) (η : P → Bool),
          compatible k (h k) u → (P.card : ℝ) ≤ Real.sqrt k →
          relativeError k u P η ≤ errorBound c k q ∧ errorBound c k q < 1 / 4) ∧
      (∀ ε : ℝ, 0 < ε → ∃ K₀ : ℕ, k₀ ≤ K₀ ∧
        ∀ (k q : ℕ) [Fact q.Prime], Odd q → parameterDomain C₀ K₀ k q → errorBound c k q < ε) := by sorry

end CyclotomicRankTwoSVP.Main
