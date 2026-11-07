-- Prove2me | Theorems.Thm_DraftPoA_path_welfare
-- name    : DraftPoA.path_welfare
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:39:30.275084+00:00
-- url     : https://prove2.me/theorems/7c96961d-ba0f-4a16-909f-5f045cb28dba
-- title:
--   §4.3: the equilibrium path, $\mathrm{SW}(b)=\sum_j\sigma_j+hr$, and $\mathrm{OPT}/\mathrm{SW}(b)\ge H_N/(\ln(H_N+1)+6)$
-- statement:
--   Let $N\ge4$, $d\ge0$ dummy items and an admissible grid $\delta'\in\{0\}\cup\{\delta_N/k:k\ge1\}$. A completion of the profile exists, and for every completion $b$:
--
--   1. the path has $N+1$ rounds; in round $t\le N$, $C_t$ takes sink item $t$ at price $\sigma_t$; in round $N+1$, $A$ takes the rent block and the dummy items at price $0$;
--   2. $\mathrm{SW}(b)=\sum_{j=1}^N\sigma_j+hr>0$, $u_A(b)=hr$, and every other bidder gets $0$;
--   3. $hr\le\ln K+4.44$ and $1+hr\le\ln K+5.44\le\ln(H_N+1)+6$;
--   4. $$\frac{\mathrm{OPT}}{\mathrm{SW}(b)}\ \ge\ \frac{H_N}{1+hr}\ \ge\ \frac{H_N}{\ln(H_N+1)+6}.$$
--
--   The bad equilibrium sells each sink item to a bidder who values it about $K$ times less than $A$, while $A$ keeps only her rent.
--
--   **Formalization Note** The ratio bounds are stated multiplied out, $\frac{H_N}{\ln(H_N+1)+6}\,\mathrm{SW}(b)\le\mathrm{OPT}$, together with $\mathrm{SW}(b)>0$.
--
--   Differences from the source:
--   - generalization: the instance with m(N) = N + r items and grid δ_N → every number d of dummy items and every grid δ′ ∈ {0} ∪ {δ_N/k : k ≥ 1}; reason: App. B (From N to m) and App. E (the verification does not use the bid increment) extend the check to these; d = 0, δ′ = δ_N is the source's case
--   - reading: the profile, with A best-responding at damaged states with F = ∅ and S ≠ ∅ → every completion (A's action free there); reason: the claim's argument does not use A's action at those states (Claim B.6, first observation)
--   - encoding: OPT/SW(b) ≥ X → X · SW(b) ≤ OPT together with SW(b) > 0; reason: equivalent; avoids real division
-- source:
--   Truong, Thach, Chan, Guo, The Price of Anarchy of Draft Auctions, STOC 2027 submission (manuscript sha256 270ffdaa…), §4.3, p.10 (PDF 11); App. B "The welfare bound", p.21 (PDF 22)

import Mathlib
import Definitions.Def_DraftPoA_Auction
import Definitions.Def_DraftPoA_BadInstance

namespace DraftPoA

/-- The equilibrium path and its welfare, §4.3, p.10 (PDF 11), with the constants of App. B
"The welfare bound", p.21 (PDF 22) (Truong, Thach, Chan, Guo, *The Price of Anarchy of Draft Auctions*, STOC 2027 submission (manuscript sha256 270ffdaa…)).

For `N ≥ 4`, any number `d` of dummy items and an admissible grid `δ′` (`0` or `δ_N/k`), a
completion of the profile exists, and for every completion `b`: the path has `N + 1` rounds; in
round `t ≤ N` bidder `C_t` takes sink item `t` at price `σ_t`; in round `N + 1` bidder `A` takes
the rent block and the dummy items for free. Hence `SW(b) = Σ_j σ_j + hr`, `A` gets `hr` and
every other bidder `0`; `hr ≤ ln K + 4.44`, `1 + hr ≤ ln K + 5.44 ≤ ln(H_N + 1) + 6`, and
`OPT/SW(b) ≥ H_N/(1 + hr) ≥ H_N/(ln(H_N + 1) + 6)`, with `SW(b) > 0`.

**Formalization Note.** Rounds are list positions (round `t` is entry `t − 1`); `C_t` is bidder
`2t`; sink item `t` is item index `t − 1`; the ratio bounds are written multiplied out. -/
theorem path_welfare (N : ℕ) (hN : 4 ≤ N) (d : ℕ) {δ' : ℝ} (hδ' : IsAdmissibleGrid N δ') :
    (∃ b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) δ' 1, IsCompletion N d b) ∧
    ∀ b : Fin (nBid N) → Strategy (nBid N) (mOf N + d) δ' 1, IsCompletion N d b →
      (play (prioBad N) b).length = N + 1 ∧
      (∀ k : ℕ, k < N → ∃ t ∈ (play (prioBad N) b)[k]?,
        t.1.val = 2 * (k + 1) ∧ t.2.1 = sigma N (k + 1) ∧
        t.2.2 = Finset.univ.filter (fun x : Fin (mOf N + d) => x.val = k)) ∧
      (∃ t ∈ (play (prioBad N) b)[N]?,
        t.1 = bidA N ∧ t.2.1 = 0 ∧
        t.2.2 = Finset.univ.filter (fun x : Fin (mOf N + d) => N ≤ x.val)) ∧
      SW (prioBad N) (vBad N d) b = ∑ j ∈ Finset.Icc 1 N, sigma N j + hOf N * rOf N ∧
      u (prioBad N) (vBad N d) b (bidA N) = hOf N * rOf N ∧
      (∀ i, i ≠ bidA N → u (prioBad N) (vBad N d) b i = 0) ∧
      0 < SW (prioBad N) (vBad N d) b ∧
      hOf N * rOf N ≤ Real.log (Kof N) + 4.44 ∧
      1 + hOf N * rOf N ≤ Real.log (Kof N) + 5.44 ∧
      Real.log (Kof N) + 5.44 ≤ Real.log ((harmonic N : ℝ) + 1) + 6 ∧
      (harmonic N : ℝ) / (1 + hOf N * rOf N) * SW (prioBad N) (vBad N d) b ≤ OPT (vBad N d) ∧
      (harmonic N : ℝ) / (Real.log ((harmonic N : ℝ) + 1) + 6) * SW (prioBad N) (vBad N d) b ≤
        OPT (vBad N d) := by sorry

end DraftPoA
