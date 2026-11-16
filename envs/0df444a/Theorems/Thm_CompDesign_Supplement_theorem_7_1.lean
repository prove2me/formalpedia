-- Prove2me | Theorems.Thm_CompDesign_Supplement_theorem_7_1
-- name    : CompDesign.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T20:59:21.783962+00:00
-- url     : https://prove2.me/theorems/54409954-251a-41d9-a140-3488ee256ad9
-- title:
--   Theorem 7.1 — single agent, $v(S)=|S|/m$: every deterministic rule has price of anarchy at least $m$, even with $c_e<B$
-- statement:
--   A single agent has actions $A=\{1,\dots,m\}$ with private costs $c_e>0$ and additive cost $c(S)=\sum_{e\in S}c_e$; a deterministic compensation rule $p:2^A\to[0,B]$ is fixed in advance, and the agent chooses a platform-favoring best response (maximizing $p(S)-c(S)$, then $v(S)$). $\mathrm{OPT}(c)=\max\{v(T):c(T)\le B\}$.
--
--   **Theorem 7.1 ($\Omega(m)$ lower bound for deterministic rules).** Fix $m\ge2$, $B>0$ and the additive value function $v(S)=|S|/m$. For every rule $p:2^A\to[0,B]$ there are costs with
--   $$0<c_e<B\qquad(e\in A)$$
--   and a platform-favoring best response $S$ with $\mathrm{OPT}(c)>0$ and $\mathrm{OPT}(c)\ge m\,v(S)$; that is, the price of anarchy of $p$ is at least $m$.
--
--   Unlike the binary-action setting, deterministic rules cannot achieve a constant price of anarchy once an agent chooses among many actions.
--
--   Differences from the source:
--   - reading: "the price of anarchy for any deterministic rule is at least m" → for every p : 2^A → [0, B], some costs 0 < c_e < B and some platform-favoring best response S with 0 < OPT and m·v(S) ≤ OPT; reason: the price of anarchy is a supremum over instances of OPT over the worst equilibrium value, with +∞ when OPT > 0 = v(S) (5)
--   - encoding: costs c_e < B → 0 < c_e < B; reason: §7.1 takes costs positive (p.52)
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), Theorem 7.1, §7.1.1, p.52 (PDF 55)

import Mathlib
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_Supplement_IsPFBestResponse

set_option autoImplicit false

open CompDesignBFM

namespace CompDesign.Supplement

/-- Theorem 7.1 (`Ω(m)` lower bound for deterministic rules), §7.1.1, p.52 (PDF 55) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026,
sha256 3d305d4d…). Fix
`m ≥ 2`, `B > 0`, and the additive value function `v(S) = |S|/m`. The price of anarchy for any
deterministic rule is at least `m` even when the costs satisfy `c_e < B` for any `e ∈ A`.

**Formalization Note.** The single agent has actions `A = Fin m`. A deterministic rule is any
`p : 2^A → [0, B]`, fixed before the costs (cost obliviousness). "PoA at least `m`" is: some cost
vector with `0 < c_e < B` (§7.1 takes costs positive) has a platform-favoring best response `S` with
`0 < OPT` and `m v(S) ≤ OPT`, the convention of (5). `OPT` is the published benchmark (4) with
actions in place of agents. -/
theorem theorem_7_1 (m : ℕ) (hm : 2 ≤ m) (B : ℝ) (hB : 0 < B) (p : Finset (Fin m) → ℝ)
    (hp : ∀ S, 0 ≤ p S ∧ p S ≤ B) :
    ∃ c : Fin m → ℝ, (∀ e, 0 < c e ∧ c e < B) ∧
      ∃ S : Finset (Fin m), IsPFBestResponse p (fun T => (T.card : ℝ) / m) c S ∧
        0 < CompDesignBFM.OPT (fun T => (T.card : ℝ) / m) B c ∧
        (m : ℝ) * ((S.card : ℝ) / m) ≤ CompDesignBFM.OPT (fun T => (T.card : ℝ) / m) B c := by sorry

end CompDesign.Supplement
