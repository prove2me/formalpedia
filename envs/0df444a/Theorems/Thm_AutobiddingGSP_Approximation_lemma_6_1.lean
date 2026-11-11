-- Prove2me | Theorems.Thm_AutobiddingGSP_Approximation_lemma_6_1
-- name    : AutobiddingGSP.Approximation.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:28:34.012859+00:00
-- url     : https://prove2.me/theorems/0df0423d-1945-4bc0-8c4c-fc4c5d24fb29
-- title:
--   Lemma 6.1 — a linear-time Gray-code extraction gadget
-- statement:
--   There is a gadget family $E_b(r;g_1,\dots,g_b)$, $b\ge1$, constructed from $b$ in $O(b)$ elementary word operations (and with polynomial-time binary serialization) and with at most $c\,b$ vertices and gates for a constant $c$, such that each $E_b$ is an acyclic Pure-Circuit gadget with one external input $r$ and $b$ distinct outputs, and in every satisfying assignment: at most one output is impure; any two pure completions $\hat g,\tilde g$ satisfy $|D_b(\hat g)-D_b(\tilde g)|\le1$; if $r=0$ every pure completion decodes to $0$, and if $r=1$ to $2^b-1$.
--
--   Differences from the source:
--   - reading: one can construct in O(b) time → LinearGadgetConstruction E: one finite program halts in at most c·b elementary word operations, with all register values at most c·(b+1); polynomial-time binary serialization is also stated; reason: the proof repeats a fixed constant-size block b times; unit-cost operations on O(log(b+1))-bit vertex indices retain its linear runtime, while a binary Turing-machine encoding needs more than O(b) output bits
--   - encoding: acyclic gadget with one external input → Gadget.WF (b distinct output vertices, input produced by no gate, every other vertex by exactly one) and a rank function increasing along every gate; reason: standard meaning of acyclic
-- source:
--   Hansen, Li and Nie (2026), Complexity of Autobidding Equilibria in GSP Sponsored Shopping, arXiv:2610.13716 [arXiv version unverified; supplied PDF revision created 2026-11-03, SHA256 40ce53fb39e7897580c44ffab04f7611388d8afc4c26ee7118de76bd21b73c8f], Lemma 6.1, pp. 27–28 (PDF 27–28)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_AutobiddingGSP_Approximation_GrayExtractor

namespace AutobiddingGSP.Approximation

/-- **Lemma 6.1 (Gray-code extraction gadget)** (Hansen, Li and Nie, *Complexity of Autobidding Equilibria in GSP Sponsored Shopping*, arXiv:2610.13716 [arXiv version unverified; supplied PDF SHA256 40ce53fb…c73c8f], pp. 27–28 (PDF 27–28)). For every `b ≥ 1` one
can construct in `O(b)` time an acyclic Pure-Circuit gadget `E_b(r; g_1, …, g_b)` with one external
input `r` and `b` output vertices such that, in every satisfying assignment, its output
`g = (g_1, …, g_b)` satisfies: (1) at most one entry of `g` is impure; (2) any two pure completions
`ĝ, g̃` have `|D_b(ĝ) − D_b(g̃)| ≤ 1`; (3) if `r = 0` every pure completion decodes to `0`, and if
`r = 1` every pure completion decodes to `2^b − 1`.

**Formalization Note** The linear runtime is measured by `LinearGadgetConstruction`: one finite
program emits basic gates and output vertices in at most `c*b` elementary word operations, with
all words bounded by `c*(b+1)`. This matches the proof's constant-size block per bit. Polynomial
time for serializing the binary code on Cook's machines is also retained. Output vertices are
distinct; both constants are uniform in `b`. -/
theorem lemma_6_1 : ∃ E : ℕ → Gadget,
    LinearGadgetConstruction E ∧
    CookPvsNP.PolyTimeComputable (fun s : List Bool => encGadget (E s.length)) ∧
    (∃ c : ℕ, ∀ b, 1 ≤ b → (E b).nV ≤ c * b ∧ (E b).gates.length ≤ c * b) ∧
    ∀ b, 1 ≤ b → (E b).IsGrayExtractor b := by sorry

end AutobiddingGSP.Approximation
