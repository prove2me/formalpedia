-- Prove2me | Theorems.Thm_DraftPoA_from_N_to_m
-- name    : DraftPoA.from_N_to_m
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:12.974917+00:00
-- url     : https://prove2.me/theorems/88c4d4d9-5cc8-4a9d-8289-9f028d279079
-- title:
--   From $N$ to $m$: $m(N)=O(N\ln N\ln\ln N)$ and $H_N/(\ln(H_N+1)+6)\ge(1-O(1/\ln\ln m))\ln m/\ln\ln m$
-- statement:
--   1. There is a constant $C$ with $m(N)\le C\,N\ln N\ln\ln N$ for all $N\ge4$.
--   2. $m(N)$ increases strictly with $N$ ($N\ge4$).
--   3. For every $m'\ge m(4)$ there is a largest $N\ge4$ with $m(N)\le m'$.
--   4. There are $C$ and $m_0$ such that for every $m'\ge m_0$ and that largest $N$,
--
--   $$\frac{H_N}{\ln(H_N+1)+6}\ \ge\ \Bigl(1-\frac{C}{\ln\ln m'}\Bigr)\frac{\ln m'}{\ln\ln m'}.$$
--
--   With the dummy items this turns the bound for $N$ sink items into the bound for every number $m'$ of items.
--
--   Differences from the source:
--   - encoding: O(N ln N ln ln N) and 1 − O(1/ln ln m) → a constant C (and a threshold m₀) quantified before N and m; reason: the meaning of O(·)
--   - reading: m(N) increases with N → m(N) < m(N + 1) for N ≥ 4; reason: strict increase is what the dummy padding uses
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), App. B "From N to m", p.21 (PDF 22)

import Mathlib
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- From N to m, App. B, p.21 (PDF 22) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

(i) `m(N) ≤ C N ln N ln ln N` for a constant `C` and all `N ≥ 4`; (ii) `m(N)` increases strictly
with `N`; (iii) for every `m′ ≥ m(4)` there is a largest `N ≥ 4` with `m(N) ≤ m′`; (iv) for that `N`,
`H_N/(ln(H_N + 1) + 6) ≥ (1 − O(1/ln ln m′)) ln m′/ln ln m′`.

**Formalization Note.** `O(1/ln ln m′)` is a constant `C` with a threshold `m₀`, both quantified
before `m′`. -/
theorem from_N_to_m :
    (∃ C : ℝ, ∀ N : ℕ, 4 ≤ N →
      (mOf N : ℝ) ≤ C * N * Real.log N * Real.log (Real.log N)) ∧
    (∀ N : ℕ, 4 ≤ N → mOf N < mOf (N + 1)) ∧
    (∀ m : ℕ, mOf 4 ≤ m → ∃ N, IsGreatest {N : ℕ | 4 ≤ N ∧ mOf N ≤ m} N) ∧
    (∃ (C : ℝ) (m₀ : ℕ), ∀ m : ℕ, m₀ ≤ m → ∀ N : ℕ, IsGreatest {N : ℕ | 4 ≤ N ∧ mOf N ≤ m} N →
      (1 - C / Real.log (Real.log m)) * (Real.log m / Real.log (Real.log m)) ≤
        (harmonic N : ℝ) / (Real.log ((harmonic N : ℝ) + 1) + 6)) := by sorry

end DraftPoA
