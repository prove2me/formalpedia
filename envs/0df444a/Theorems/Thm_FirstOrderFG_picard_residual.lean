-- Prove2me | Theorems.Thm_FirstOrderFG_picard_residual
-- name    : FirstOrderFG.picard_residual
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:49:48.214327+00:00
-- url     : https://prove2.me/theorems/57dc49cb-ce5c-4cc4-9b48-5afe17300ea5
-- title:
--   Proof of Proposition A.3 — Picard residual $\|q^{(n)}-F_{p,\gamma}(q^{(n)})\|_1\le D_n\le C_\gamma^{n-1}D_1\le2C_\gamma^{n-1}|\ln(\gamma KT)|$
-- statement:
--   Throughout, $G=(V,E)$ is a strongly observable directed graph on $K\ge2$ arms ($i\to j$: playing $i$ reveals the loss of $j$), $T\ge3$ is the horizon, and the oblivious adversary fixes losses $\ell_1,\dots,\ell_T\in[0,1]^K$ in advance.
--
--   Let $p$ be in the interior of $\Delta(V_{\mathrm{self}})$, $\gamma>0$, and $q^{(0)}$ any interior point of $\Delta(V_{\mathrm{self}})$; let $q^{(n+1)}=F_{p,\gamma}(q^{(n)})$ and
--   $$
--   C_\gamma=\frac{|\sqrt{\gamma KT}-1|}{\sqrt{\gamma KT}+1},\qquad D_n=\max_{i\in V_{\mathrm{self}}}\ln\frac{q^{(n+1)}_i}{q^{(n)}_i}-\min_{i\in V_{\mathrm{self}}}\ln\frac{q^{(n+1)}_i}{q^{(n)}_i}.
--   $$
--   Then:
--   1. for every $n\ge1$,
--   $$
--   \|q^{(n)}-F_{p,\gamma}(q^{(n)})\|_1\le D_n\le C_\gamma^{\,n-1}D_1\le 2C_\gamma^{\,n-1}|\ln(\gamma KT)| ;
--   $$
--   2. every iterate $q^{(n)}$ lies in the interior of $\Delta(V_{\mathrm{self}})$;
--   3. for every $\varepsilon>0$ some $n\ge1$ has $\|q^{(n)}-F_{p,\gamma}(q^{(n)})\|_1\le\varepsilon$.
--
--   Since $C_\gamma<1$, the residual decays geometrically, so the Picard iteration in line 6 of Algorithm 2 terminates at an interior $\varepsilon$-fixed point.
--
--   Differences from the source:
--   - generalization: the display $\|q^{(n)}-F_{p,\gamma}(q^{(n)})\|_1\le D_n\le C_\gamma^{n-1}D_1\le2C_\gamma^{n-1}|\ln(\gamma KT)|$ (p.20) → the display together with two consequences used on pp.20–21: the iterates stay interior, and the residual is $\le\varepsilon$ for some $n\ge1$; reason: the Lean statement contains the display as its first clause, so it specializes to it
--   - encoding: $\ell_1$ norm on $\Delta(V_{\mathrm{self}})$ → sum over $V_{\mathrm{self}}$ of functions on all arms; reason: distributions on $V_{\mathrm{self}}$ are read on $V_{\mathrm{self}}$ only; same values
-- source:
--   Zhang–Zhang–Luo–Mineiro, Near-Optimal First-Order Regret for Bandits with Feedback Graphs, arXiv:2610.40861, proof of Proposition A.3, pp.20–21

import Mathlib
import Definitions.Def_FirstOrderFG_StronglyObservable
import Definitions.Def_FirstOrderFG_fixResidual
import Definitions.Def_FirstOrderFG_logSpread
import Definitions.Def_FirstOrderFG_picardIter

namespace FirstOrderFG

/-- **Geometric decay of the Picard residual (proof of Proposition A.3).** Zhang–Zhang–Luo–Mineiro, *Near-Optimal First-Order Regret for Bandits with Feedback Graphs*, arXiv:2610.40861, proof of
Proposition A.3, pp.20–21: with `C_γ ≜ |√(γKT) − 1|/(√(γKT) + 1)` and `D_n` the spread of
`ln(q_i^{(n+1)}/q_i^{(n)})` over `V_self`, "Combining this bound with Eq. (59) gives
`‖q^{(n)} − F_{p,γ}(q^{(n)})‖₁ ≤ D_n ≤ C_γ^{n−1} D_1 ≤ 2C_γ^{n−1} |ln(γKT)|`", for
`p ∈ int(∆(V_self))`, `γ > 0`, any `q^{(0)} ∈ int(∆(V_self))` and every `n ≥ 1`.

Also: the iterates stay in `int(∆(V_self))`, and (p.21) for every `ε > 0` some `n ≥ 1` has residual
at most `ε`, so the iteration of Algorithm 2, line 6, terminates.

**Formalization Note.** `‖·‖₁` is summed over `V_self`. -/
theorem picard_residual {K : ℕ} (T : ℕ) (hK : 2 ≤ K) (hT : 3 ≤ T)
    (E : Fin K → Fin K → Prop) [DecidableRel E] (hSO : StronglyObservable E)
    (p : Fin K → ℝ) (hp : ∀ i ∈ Vself E, 0 < p i) (hp1 : ∑ i ∈ Vself E, p i = 1)
    (γ : ℝ) (hγ : 0 < γ) (q0 : Fin K → ℝ) (hq0 : ∀ i ∈ Vself E, 0 < q0 i)
    (hq01 : ∑ i ∈ Vself E, q0 i = 1) :
    let Cγ := |Real.sqrt (γ * K * T) - 1| / (Real.sqrt (γ * K * T) + 1)
    (∀ n : ℕ, 1 ≤ n →
      fixResidual E T p γ (picardIter E T p γ q0 n) ≤ logSpread E T p γ q0 n ∧
      logSpread E T p γ q0 n ≤ Cγ ^ (n - 1) * logSpread E T p γ q0 1 ∧
      Cγ ^ (n - 1) * logSpread E T p γ q0 1 ≤ 2 * Cγ ^ (n - 1) * |Real.log (γ * K * T)|) ∧
    (∀ n : ℕ, (∀ i ∈ Vself E, 0 < picardIter E T p γ q0 n i) ∧
      ∑ i ∈ Vself E, picardIter E T p γ q0 n i = 1) ∧
    (∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 1 ≤ n ∧ fixResidual E T p γ (picardIter E T p γ q0 n) ≤ ε) := by sorry

end FirstOrderFG
