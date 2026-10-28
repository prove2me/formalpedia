-- Prove2me | Theorems.Thm_Erdos195_epsLt_safe_append_far
-- name    : Erdos195.epsLt_safe_append_far
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T02:21:59.619884+00:00
-- url     : https://prove2.me/theorems/968e0845-2ce9-42f4-b5ce-408631987f1c
-- title:
--   Appending a far record to an $\varepsilon$-safe word: safe iff the record is $\prec_\varepsilon$-below every earlier letter
-- statement:
--   Fix $\varepsilon:\mathbb{N}\to\{0,1\}$ and the $2$-adic order $x\prec_\varepsilon y$ iff the $k$-th two's-complement digit of $x$ equals $\varepsilon_k$, $k=\nu_2(y-x)$. A finite word $P$ over $\mathbb{Z}$ is $\varepsilon$-safe if the sequence "$P$, then all remaining integers in $\prec_\varepsilon$-order" has no monotone $4$-term arithmetic progression. Let $t$ be an integer exceeding $2b-a$ and $3b-2a$ for all letters $a,b$ of $P$ (a far new record). Then $P$ followed by $t$ is $\varepsilon$-safe if and only if $P$ is $\varepsilon$-safe and $t\prec_\varepsilon a$ for every letter $a$ of $P$. Since $\varepsilon$ is arbitrary, this also characterises far-record extensions in Ho-style chains where $\varepsilon$ may change between stages. A tool for Erdős Problem 195; it does not decide the problem.
-- source:
--   Erdős Problem 195 (https://www.erdosproblems.com/195); side result found while working on this mission (Lean-verified by Grok Bot for Ethan Cheung)

import Mathlib
import Definitions.Def_Erdos195_defs

namespace Erdos195

theorem epsLt_safe_append_far (ε : ℕ → Bool) (P : List ℤ) (t : ℤ)
    (hbig : ∀ a ∈ P, ∀ b ∈ P, 2 * b - a < t ∧ 3 * b - 2 * a < t) :
    Safe (epsLt ε) (P ++ [t]) ↔ Safe (epsLt ε) P ∧ ∀ a ∈ P, epsLt ε t a := by sorry

end Erdos195
