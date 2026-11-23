-- Prove2me | Theorems.Thm_ChenCapacityTerminals_Exact_terminal_expansion
-- name    : ChenCapacityTerminals.Exact.terminal_expansion
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T06:22:25.193511+00:00
-- url     : https://prove2.me/theorems/6bf06344-407a-44ef-adcd-35ce56180557
-- title:
--   Theorem 2.1 — weighted separator expansion after deleting marked components
-- statement:
--   Fix a legal construction on a prepared rooted network and write $P$ for its selected terminals and $C_d=4d(3+\lceil\log_2 n\rceil)$. If $L$ is a lower bound on every nonempty root-avoiding entering cut, then every $X\subseteq V\setminus(P\cup\{r\})$ satisfies
--
--   $$
--   b(X)\le C_d\,t\,\frac{f(X)}L.
--   $$
--
--   After removing all early probes and strict postorder marks, each surviving component of the guide induced by $X$ has mass at most $t$. The number of such components is the number of entering guide edges, so Lemma 2.3 and $\tau=L/(4d)$ give the sharper factor $4d(1+\min\{R,\lfloor\log_2n\rfloor\})$, which is bounded by $C_d$. Even if $r$ itself was marked, no omitted root mark can occur in $X$.
--
--   Consequently, for unit masses and $t=d$, the same argument yields $|X|\le C_d\,d\,f(X)/L$. Empty $X$ and zero-valued cuts are included.
-- source:
--   Thomas Chen, STOC 2027 submission #665 (October 2026), Theorem 2.1 equation (2) and §2.3 “Weighted separation and implementation”, pp. 3–5, PDF pp. 4–7, using Lemma 2.3 on PDF p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/665.pdf#page=6

import Definitions.Def_ChenCapacityTerminals_Exact_Specifications

set_option autoImplicit false

open ChenCapacityTerminals.Exact

theorem ChenCapacityTerminals.Exact.terminal_expansion
    (G : Network) (r d : ℕ) (L : ℚ) (b : ℕ → ℕ) (t : ℕ) (c : Construction)
    (hG : Prepared G r) (hd : 1 ≤ d) (hdn : d ≤ G.vertices.card)
    (hL : 0 < L) (ht : 1 ≤ t) (hc : LegalConstruction G r d L b t c) :
    (RootLowerBound G r L → ∀ X ⊆ G.vertices \
      (c.terminals G r ((L : ℝ) / (4 * d)) b t ∪ {r}),
      (mass b X : ℝ) ≤ (terminalCoefficient G.vertices.card d : ℝ) * t * cut G X / L) ∧
    ((∀ v ∈ G.vertices, b v = 1) → t = d → RootLowerBound G r L →
      ∀ X ⊆ G.vertices \ (c.terminals G r ((L : ℝ) / (4 * d)) b t ∪ {r}),
        (X.card : ℝ) ≤ (terminalCoefficient G.vertices.card d : ℝ) * d * cut G X / L) := by sorry
