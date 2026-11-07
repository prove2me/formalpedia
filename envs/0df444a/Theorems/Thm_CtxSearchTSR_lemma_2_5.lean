-- Prove2me | Theorems.Thm_CtxSearchTSR_lemma_2_5
-- name    : CtxSearchTSR.lemma_2_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:09.76057+00:00
-- url     : https://prove2.me/theorems/5b28671f-8d8d-4607-9e8e-12eb83ebd5c0
-- title:
--   Lemma 2.5 — one-round potential decrease $\mathbb E_t[\ell_t]\le6(\Phi_t-\mathbb E_t[\Phi_{t+1}])$
-- statement:
--   On every round of Algorithm 2,
--
--   $$\mathbb E_t[\ell_t]\le6\bigl(\Phi_t-\mathbb E_t[\Phi_{t+1}]\bigr), \tag{13}$$
--
--   where $\mathbb E_t$ is the expectation conditional on the history and the current context, i.e. over the fresh sign $\varepsilon_t$ only.
--
--   Precisely: let $(\mathbf m,R)$ be a state with $R\succ0$, $\mathbf z\in\mathbb R^d$, and $x$ a context with $\|x\|_2\le1$. For $\varepsilon\in\{-1,1\}$ let $P(\varepsilon)$ be the price (9) and $(\mathbf m_+(\varepsilon),R_+(\varepsilon))$ the update (10) with the algorithm's answer $Y=\operatorname{sign}(x^\top\mathbf z-P(\varepsilon))$. Then
--
--   $$\frac12\sum_{\varepsilon=\pm1}\bigl|x^\top\mathbf z-P(\varepsilon)\bigr|\ \le\ 6\Bigl(\Phi(\mathbf m,R,\mathbf z)-\frac12\sum_{\varepsilon=\pm1}\Phi\bigl(\mathbf m_+(\varepsilon),R_+(\varepsilon),\mathbf z\bigr)\Bigr).$$
--
--   Summing (13) over the rounds gives Theorem 2.4.
--
--   **Formalization Note** $x=0$ is allowed; both sides are then $0$.
--
--   Differences from the source:
--   - encoding: 𝔼_t = 𝔼[· | F_{t−1}, x_t] on a round of Algorithm 2 → the average over the fresh sign at a fixed state (m, R) and context x; reason: given the history and the current context the state is fixed and the fresh sign is the only randomness
--   - generalization: on every round of Algorithm 2 (reachable states, target with ‖z‖₂ ≤ 1) → every state with R ≻ 0 and every z ∈ ℝ^d; reason: every reachable state has R ≻ 0 (§2.2), and the proof uses only R ≻ 0 and ‖x‖₂ ≤ 1; it specializes to every round
--   - encoding: the update (10) at x_t = 0 (a_t = 0, the division in (10) is undefined; the paper says the loss and potential change are both zero, App. C.3, p.21) → Lean's c/0 = 0 makes the update the identity and the price x⊤m + 0 = 0; reason: the paper's own convention for x_t = 0; no instance changes
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §2.2, Lemma 2.5, p.11, (13); proof App. C.3, pp.21–22

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2
import Definitions.Def_CtxSearchTSR_Potentials

open Matrix

namespace CtxSearchTSR

/-- **Lemma 2.5 (One-round potential decrease).** Cosson et al., *Contextual Search and Bilateral Trade with a Trace-Square-Root Potential*, STOC 2027
submission (manuscript sha256 70eeb0d1…), p.11, (13); proof App. C.3,
pp.21–22.

"On every round of Algorithm 2, 𝔼_t[ℓ_t] ≤ 6(Φ_t − 𝔼_t[Φ_{t+1}])." (13)

𝔼_t conditions on the history and the current context, so at a round with state (**m**, R) and
context x the only randomness is the fresh sign ε. For every state with R ≻ 0, every target **z**
and every context with ‖x‖₂ ≤ 1:

(1/2) Σ_{ε=±1} |xᵀ**z** − P(ε)| ≤ 6 (Φ(**m**, R, **z**) − (1/2) Σ_{ε=±1} Φ(**m**₊(ε), R₊(ε), **z**)),

where P(ε) is the price (9) and (**m**₊(ε), R₊(ε)) is the update (10) with the algorithm's answer
Y = sign(xᵀ**z** − P(ε)).

**Formalization Note.** The statement holds at every state with R ≻ 0, which includes every state
the algorithm reaches (`section_2_2_posDef_preserved`), and at every target. x = 0 is allowed. -/
theorem lemma_2_5 {d : ℕ} (z : Fin d → ℝ) (s : State d) (hR : s.R.PosDef) (x : Fin d → ℝ)
    (hx : eucNorm x ≤ 1) :
    (∑ b : Bool, searchLoss z x (price s x (signOf b))) / 2 ≤
      6 * (Phi s.m s.R z - (∑ b : Bool, Phi (step z s x b).m (step z s x b).R z) / 2) := by sorry

end CtxSearchTSR
