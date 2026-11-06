-- Prove2me | Theorems.Thm_FixedMachinePrec_lemma_6_1
-- name    : FixedMachinePrec.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:06:34.674684+00:00
-- url     : https://prove2.me/theorems/c0ab6f62-5e55-4d8a-92c6-b8f4f481e0ac
-- title:
--   Lemma 6.1 — number of candidates $|\mathcal F_K|\le 2\cdot160^K(N+2)^{mK}$
-- statement:
--   Let $m\ge3$, $N\ge m$ and $J=\{1,\dots,N\}$. For every $K\ge1$,
--   $$B:=|\mathcal F_K|\le B_0:=2\cdot160^K(N+2)^{mK}.$$
--   For the node and cut budgets this gives
--   $$B_{\mathrm{node}}\le 2\cdot160^{4m+5}(N+2)^{4m^2+5m},\qquad B_{\mathrm{cut}}\le 2\cdot160^{m+3}(N+2)^{m^2+3m}.$$
--
--   These bounds make the candidate families polynomial in $N$ for every fixed $m$.
--
--   **Formalization Note** The bound is stated for every relation and every rank function: it counts formulas over the $5\binom Nm+N+3$ atom names.
--
--   Differences from the source:
--   - generalization: the padded order and its topological rank → every relation prec and every rank function; reason: the count depends only on the number of atom names; the padded order and its rank are one case
--   - encoding: jobs 1, …, n and padded jobs 1, …, N → Fin n and Fin N (0-based labels); reason: Lean convention; the shift changes no instance
-- source:
--   K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, manuscript dated 1 November 2026 (sha256 08cdf3e1…), Lemma 6.1, p.21

import Mathlib
import Definitions.Def_FixedMachinePrec_Formula

namespace FixedMachinePrec

/-- **Lemma 6.1 (Number of candidates).** Jansen, *Precedence Constraint Scheduling on a Fixed
Number of Machines* (manuscript, sha256 08cdf3e1…), Lemma 6.1, p.21: "For m ≥ 3, N ≥ m, and
K ≥ 1, the family size satisfies B := |F_K| ≤ B_0 := 2 · 160^K (N + 2)^{mK}. For the node and cut
budgets, respectively, this gives B_node ≤ B_node,0 := 2 · 160^{4m+5} (N + 2)^{4m²+5m},
B_cut ≤ B_cut,0 := 2 · 160^{m+3} (N + 2)^{m²+3m}."

**Formalization Note** `J = Fin N`. The bound is stated for every relation `prec` and every rank
function `rank`: the count uses only the number of atom names, `5·C(N, m) + N + 3`, so it holds in
particular for the padded order and its topological rank. -/
theorem lemma_6_1 {N : ℕ} (m : ℕ) (hm : 3 ≤ m) (hN : m ≤ N) (prec : Fin N → Fin N → Prop)
    [DecidableRel prec] (rank : Fin N → ℕ) :
    (∀ K : ℕ, 1 ≤ K → (family prec rank m K).card ≤ 2 * 160 ^ K * (N + 2) ^ (m * K)) ∧
    (family prec rank m (4 * m + 5)).card ≤ 2 * 160 ^ (4 * m + 5) * (N + 2) ^ (4 * m ^ 2 + 5 * m) ∧
    (family prec rank m (m + 3)).card ≤ 2 * 160 ^ (m + 3) * (N + 2) ^ (m ^ 2 + 3 * m) := by sorry

end FixedMachinePrec
