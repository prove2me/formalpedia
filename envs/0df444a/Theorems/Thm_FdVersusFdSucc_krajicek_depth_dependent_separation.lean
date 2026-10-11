-- Prove2me | Theorems.Thm_FdVersusFdSucc_krajicek_depth_dependent_separation
-- name    : FdVersusFdSucc.krajicek_depth_dependent_separation
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T10:16:02.080397+00:00
-- url     : https://prove2.me/theorems/2c30291b-0de2-4939-bf1a-95fca370ef2a
-- title:
--   Separation of $F_{d+1}$ from $F_d$ by depth-$d$ tautologies
-- statement:
--   There is $d_0$ such that for every $d\ge d_0$ there is a family $(\tau_m)_{m\in\mathbb N}$ of tautologies of depth at most $d$ with $|\tau_m|\ge m$ such that
--
--   1. for some $C$, each $\tau_m$ has an $F_{d+1}$-proof of size at most $C\,|\tau_m|^{C}$;
--   2. for some $\varepsilon>0$ and all sufficiently large $m$, every $F_d$-proof of $\tau_m$ has size at least $2^{|\tau_m|^{\varepsilon}}$.
--
--   This is the case of the problem in which the depth $k$ of the tautologies may depend on $d$ (with $k=d$), recorded as known on the Open Problem Garden page.
--
--   **Formalization Note** The statement is asked only for all sufficiently large $d$, to be robust to the offset between depth conventions (here literals have depth $0$; in this convention the statement fails for $d=1$, since depth-1 tautologies have linear-size $F_1$-proofs).
-- source:
--   J. Krajíček, Lower bounds to the size of constant-depth propositional proofs, J. Symbolic Logic 59(1), 1994, 73-86; stated as known (k := d) on Open Problem Garden, 'F_d versus F_{d+1}' (J. Krajíček), http://www.openproblemgarden.org/op/f_d_versus_f_d_1

import Definitions.Def_FdVersusFdSucc_defs

open Filter

namespace FdVersusFdSucc

/-- (Krajíček 1994, as recorded on the Open Problem Garden page: the problem is solved when `k`
may depend on `d`, with `k := d`.) For all sufficiently large `d` there is a sequence of
depth-`d` tautologies with polynomial-size `F_{d+1}`-proofs that require exponential-size
`F_d`-proofs. -/
theorem krajicek_depth_dependent_separation :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∃ τ : ℕ → Formula, PolySeparates d d τ := by sorry

end FdVersusFdSucc
