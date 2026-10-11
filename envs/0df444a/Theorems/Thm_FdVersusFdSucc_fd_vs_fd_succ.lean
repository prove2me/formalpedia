-- Prove2me | Theorems.Thm_FdVersusFdSucc_fd_vs_fd_succ
-- name    : FdVersusFdSucc.fd_vs_fd_succ
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:16:34.526982+00:00
-- url     : https://prove2.me/theorems/04b35ab1-4dc5-40c1-931a-b70cbfdae146
-- title:
--   $F_d$ versus $F_{d+1}$: a fixed depth $k$ separating all consecutive levels
-- statement:
--   There is a constant $k$ such that for every $d\ge k$ there is a family $(\tau_m)_{m\in\mathbb N}$ of tautologies of depth at most $k$ with $|\tau_m|\ge m$ such that
--
--   1. (quasi-polynomial upper bound) for some $C$, each $\tau_m$ has an $F_{d+1}$-proof of size at most $2^{C(\log_2|\tau_m|)^{C}}$;
--   2. (exponential lower bound) for some $\varepsilon>0$ and all sufficiently large $m$, every $F_d$-proof of $\tau_m$ has size at least $2^{|\tau_m|^{\varepsilon}}$.
--
--   In symbols:
--   $$\exists k\ \forall d\ge k\ \exists \tau:\ \mathrm{QuasiPolySeparates}(k,d,\tau).$$
--
--   This is Krajíček's open problem: one extra level of proof depth gives an exponential speed-up already on tautologies of one fixed depth.
--
--   **Formalization Note** The problem says "for any $d$"; since a depth-$k$ formula has no $F_{d+1}$-proof when $d+1<k$, the statement is taken for $d\ge k$. The problem allows a polynomial or quasi-polynomial upper bound; the goal uses the weaker (quasi-polynomial) one, so a polynomial solution also proves it.
-- source:
--   Open Problem Garden, 'F_d versus F_{d+1}' (J. Krajíček), http://www.openproblemgarden.org/op/f_d_versus_f_d_1 (problem statement); J. Krajíček, Bounded arithmetic, propositional logic, and complexity theory, CUP 1995, p. 243.

import Definitions.Def_FdVersusFdSucc_defs

open Filter

namespace FdVersusFdSucc

/-- **Goal** (Krajíček; Open Problem Garden "F_d versus F_{d+1}"). There is a constant `k`
such that for every `d ≥ k` there is a sequence of depth-`k` tautologies with
quasi-polynomial-size proofs in `F_{d+1}` that require exponential-size proofs in `F_d`. -/
theorem fd_vs_fd_succ :
    ∃ k : ℕ, ∀ d : ℕ, k ≤ d → ∃ τ : ℕ → Formula, QuasiPolySeparates k d τ := by sorry

end FdVersusFdSucc
