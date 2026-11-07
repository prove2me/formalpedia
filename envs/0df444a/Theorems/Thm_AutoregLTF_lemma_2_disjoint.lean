-- Prove2me | Theorems.Thm_AutoregLTF_lemma_2_disjoint
-- name    : AutoregLTF.lemma_2_disjoint
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:55:21.616558+00:00
-- url     : https://prove2.me/theorems/5d398370-cb09-4323-bb11-c628b4a21651
-- title:
--   Proof of Lemma 2, p.9 — the updates (22)–(23) are disjoint from each other and from (17)–(18)
-- statement:
--   Let $m\ge2$ and $\theta\in\{0,\dots,2^m-1\}^m$. The coordinates updated in (22) and (23),
--
--   $$1,\ p-1,\ p,\ p+1,\ \pi(\mathrm{test}),\ \pi(\mathrm{out},j)\ (j\in[m]),\ \pi(\mathrm{ptr},j)\ (j\in[m+1]),\ \pi(b)+1\ (\text{all } b),\ \text{and } p/3<\ell\le2p/3,$$
--
--   are pairwise distinct, lie in $[p+1]$, and none of them is an index assigned in (17)–(18).
--
--   Together with Claim 1, this makes the final coefficient vector $a$ of Lemma 2 well defined.
--
--   Differences from the source:
--   - generalization: "These assignments are disjoint from each other and from (17)–(18)" → disjointness, plus: every index of (22)–(23) lies in [p + 1]; reason: the paper presupposes the range (a is a vector a_1, …, a_{p+1}); the Lean statement specializes to the sentence
--   - encoding: the assignments (22)–(23) and (17)–(18) → the lists assignUpd m and assign0 m θ; reason: explicit lists make the disjointness a statement rather than a convention
--   - encoding: θ ∈ {0, …, 2^m − 1}^m → θ : ℕ → ℤ with 0 ≤ θ j ≤ 2^m − 1 for j ∈ [m]; reason: only θ_1, …, θ_m are read and every vector in the range extends to such a function; same instances
-- source:
--   Doron-Arad, Mehalel, Mossel, On the VC Dimension of Autoregressive Linear Threshold Functions, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e), proof of Lemma 2, sentence after (23), p.9

import Mathlib
import Definitions.Def_AutoregLTF_coef

namespace AutoregLTF

/-- **Proof of Lemma 2**, the assignments (22)–(23) are disjoint, p.9 (PDF p.9).

I. Doron-Arad, I. Mehalel, E. Mossel, *On the VC Dimension of Autoregressive Linear Threshold
Functions*, arXiv:2610.36970 (version of 2026-11-02, sha256 e3428ab7…91c9e).

"These assignments are disjoint from each other and from (17)–(18), by their index ranges and
residues modulo 3."

Stated on the lists: the indices of `assignUpd m` ((22) and (23)) are pairwise distinct, lie in
`[p + 1]`, and none of them is an index of `assign0 m θ` ((17)–(18)).

**Formalization Note.** Hypotheses are those of Lemma 2: `m ≥ 2` (p.4) and
`θ ∈ {0, …, 2^m − 1}^m`. The range conjunct (every index of (22)–(23) lies in `[p + 1]`) is presupposed
by the paper, whose `a` is a vector `a_1, …, a_{p+1}`. With Claim 1, this makes `aCoef m θ` the paper's
`a` regardless of the lookup order. -/
theorem lemma_2_disjoint (m : ℕ) (hm : 2 ≤ m) (θ : ℕ → ℤ)
    (hθ : ∀ j ∈ Finset.Icc 1 m, 0 ≤ θ j ∧ θ j ≤ 2 ^ m - 1) :
    ((assignUpd m).map Prod.fst).Nodup ∧
    (∀ e ∈ assignUpd m, 1 ≤ e.1 ∧ e.1 ≤ (p m : ℤ) + 1) ∧
    ∀ e ∈ assignUpd m, ∀ e' ∈ assign0 m θ, e.1 ≠ e'.1 := by sorry

end AutoregLTF
