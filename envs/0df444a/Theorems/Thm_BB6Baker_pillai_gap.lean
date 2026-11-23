-- Prove2me | Theorems.Thm_BB6Baker_pillai_gap
-- name    : BB6Baker.pillai_gap
-- status  : Open
-- author  : @alon yuval
-- created : 2026-11-23T17:54:32.574604+00:00
-- url     : https://prove2.me/theorems/f255b8fc-bfc7-4422-bf90-a5e662a3588d
-- title:
--   Pillai-type gap $|2\cdot 3^i - c\cdot 2^k| > i+5$ for $i \ge 2^{60}$, $c \le 4i$ (removes a Baker axiom from a BB(6) proof)
-- statement:
--   **Theorem.** For all integers $i \ge 2^{60}$, $1 \le c \le 4i$ and $k$ with $2^k \ge 3^i/(2i)$,
--   $$\bigl|2\cdot 3^i - c\cdot 2^k\bigr| > i + 5.$$
--
--   **Why it matters.** The BB(6) holdout `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` (analysis by mxdys) never halts provided the odd part of $2\cdot 3^i + i + 5$ is at least $2i + 14$ for all $i \ge 50$. A Lean proof of this (github.com/rwst/bbchallenge, CC0) handles $50 \le i < 2^{60}$ unconditionally (2-adic Hensel lifting). For $i \ge 2^{60}$ it uses exactly this inequality (lemma `direct_pillai_bound_small` in `Ellison.lean`), which is currently derived from an **axiom** stating the Baker–Wüstholz theorem. Proving this statement in Lean would make the non-halting proof of that machine fully unconditional.
--
--   **Known proofs.** It follows from effective lower bounds for linear forms in three logarithms, $\Lambda = (k-1)\log 2 - i\log 3 + \log c$ (Baker–Wüstholz 1993, Matveev 2000, or Laurent's interpolation determinants), since a violation forces $0 < |\Lambda| \lesssim (i+5)/3^i$, while those bounds give $|\Lambda| \ge \exp(-C \log i \cdot \log(4i))$. No elementary proof is known: 2-adic and 3-adic arguments are circular for a single $i$, and two-logarithm irrationality measures for $\log 3/\log 2$ do not cover the varying $c$. A suggested roadmap is to formalize the special case $K = \mathbb{Q}$, $n = 3$, $\alpha = (2, 3, c)$ of Laurent's method: a zero estimate, an analytic upper bound for an interpolation determinant, an arithmetic (Liouville) lower bound, and an explicit choice of parameters.
-- source:
--   rwst/bbchallenge (CC0), directory 1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---, Ellison.lean `direct_pillai_bound_small` and BakerWustholz.lean axiom `bakerWustholz_linearForms_logs`; https://wiki.bbchallenge.org/wiki/1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---; Baker & Wüstholz, J. reine angew. Math. 442 (1993) 19–62.

import Mathlib

namespace BB6Baker
theorem pillai_gap (i k c : ℕ) (hi : 2 ^ 60 ≤ i) (hc : 0 < c) (hc4 : c ≤ 4 * i)
    (hk : 3 ^ i ≤ 2 * i * 2 ^ k) :
    (i : ℤ) + 5 < |2 * 3 ^ i - (c : ℤ) * 2 ^ k| := by
  sorry
end BB6Baker
