-- Prove2me | Theorems.Thm_BorderDiffEq_Supplement_theorem_2_2
-- name    : BorderDiffEq.Supplement.theorem_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:54:36.947483+00:00
-- url     : https://prove2.me/theorems/a5e5f45d-cc9a-4197-a861-9a58ce8c9a55
-- title:
--   Theorem 2.2 — explicit hitting sets of size $s^{O(k^2)}$ for border depth-3 circuits
-- statement:
--   Let $F$ be a field of characteristic zero, $k\ge1$ and $s\ge2$. There is an **explicit** hitting set for the border $\overline{\Sigma^{[k]}\Pi\Sigma(s)}$ of depth-3 circuits with at most $k$ product gates and size at most $s$, of size $s^{O(k^2)}$, which can be constructed in time $s^{O(k^2)}$.
--
--   Precisely: there are an absolute constant $C$ and one finite multi-stack Turing machine $M$ such that for all $n,k,s$ with $k\ge1$, $s\ge2$ and $n\le s$, $M$ on input $(n,k,s)$ (in binary) halts within $s^{Ck^2}$ steps, and its output is a list $H\subseteq\mathbb Q^n$ of at most $s^{Ck^2}$ points such that for every field $F$ of characteristic zero and every nonzero $f\in\overline{\Sigma^{[k]}\Pi\Sigma(s)}\subseteq F[x_1,\dots,x_n]$ some $h\in H$ has $f(h)\ne0$.
--
--   This improves the previous hitting sets of size $s^{O(k\,7^k\log\log s)}$ and has polynomial size for constant $k$.
--
--   **Formalization Note** The border is the published `BorderDiffEq.InBorderSPS` (constants in $F((\epsilon))$, size counting each factor with multiplicity plus the variables it uses). The machine model is the published `HMBinPacking.OutputsWithin` (Mathlib's `TM2OutputsInTime` with Boolean alphabets); the parameters are written by `HSSym.encodeInput` and the output is decoded into points by `HSSym.decodeOutput`.
--
--   Differences from the source:
--   - reading: "explicit hitting set … constructed in time $s^{O(k^2)}$" (no machine model fixed) → one finite multi-stack Turing machine with Boolean input and output alphabets (`Turing.TM2ComputableAux Bool Bool`) for all $(n,k,s)$ writes the points within $s^{Ck^2}$ steps; its output decodes to the hitting set; reason: explicit means a uniform construction; a single finite machine cannot hard-code infinitely many answers, and $s^{O(k^2)}$ absorbs polynomial overheads between machine models
--   - reading: number of variables not stated → $n\le s$; reason: the paper uses that the number of variables is at most the size (p.5, p.44) and assumes $n,d,k\le s$ in the proof (p.53)
--   - generalization: a hitting set in $F^n$ for the fixed field $F$ → one set of rational points that hits the class over every field of characteristic zero; reason: $\mathbb Q\subseteq F$; one set for all $F$ specializes to each $F$
--   - generalization: border constants in $F(\epsilon)$ and $f+\epsilon g$ with $g\in F[\epsilon][x]$ → constants in $F((\epsilon))$ and $f+\epsilon S$ with $S\in F[[\epsilon]][x]$ (the published `IsEpsApprox`); reason: $F(\epsilon)\subset F((\epsilon))$ and $F[\epsilon]\subset F[[\epsilon]]$, so every presentation of the paper is one here; the statement covers the paper's
--   - encoding: $s^{O(k^2)}$ → $s^{C k^2}$ with one absolute $C$ chosen before the machine and all parameters; reason: reading of $O(\cdot)$; $s\ge2$
--   - encoding: variables $x_1,\dots,x_n$ → `Fin n` (0-indexed); reason: Lean convention; same instances
-- source:
--   Bhat–Dutta–Kaplan–Shpilka–Shringi, Demystifying Border of Structured Algebraic Circuits via Differential Equations, manuscript (STOC 2027 submission; preprint basis, sha256 583bcc89e7078b50ae14babedf540a37b37e36912abda1931e4aaeb64bc57db8), Theorem 2.2, p.7; proof §7.1 (Lemmas 7.1, 7.2), pp.50–53

import Mathlib
import Definitions.Def_BorderDiffEq_InBorderSPS
import Definitions.Def_BorderDiffEq_Supplement_HSSym
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_BorderDiffEq_Supplement_RatHits

namespace BorderDiffEq.Supplement

open BorderDiffEq

/-- **Theorem 2.2 (hitting sets for border depth-3 circuits)** (Bhat–Dutta–Kaplan–Shpilka–Shringi, *Demystifying Border of Structured Algebraic Circuits
via Differential Equations*, manuscript (STOC 2027 submission), Theorem 2.2, p.7; proof §7.1,
pp.50–53). Let `k ≥ 1` and `s ≥ 2` be integers. There is an explicit hitting set for
`cl(Σ^{[k]}ΠΣ(s))` of size `s^{O(k²)}`, which can be constructed in time `s^{O(k²)}`.

**Formalization Note.** One finite multi-stack Turing machine `M` with Boolean input and
output alphabets (the published `HMBinPacking.OutputsWithin`, i.e. Mathlib's `TM2OutputsInTime`)
serves all parameters: on the bit code of `(n, k, s)` (`HSSym.encodeInput`) it halts within `s^{C·k²}` steps, and its
output decodes (`HSSym.decodeOutput`) to a list of at most `s^{C·k²}` points of `ℚⁿ` that hits every
nonzero polynomial in the border `InBorderSPS F n k s`, over every field `F` of characteristic
zero. `O(k²)` is one absolute constant `C`, chosen before the machine and every
parameter. The
number of variables satisfies `n ≤ s`, as in the proof (p.53: "using `n, d, k ≤ s`"). -/
theorem theorem_2_2 : ∃ C : ℕ, ∃ M : Turing.TM2ComputableAux Bool Bool,
    ∀ n k s : ℕ, 1 ≤ k → 2 ≤ s → n ≤ s →
    ∃ out : List Bool,
      HMBinPacking.OutputsWithin M (HSSym.encodeInput [n, k, s]) out (s ^ (C * k ^ 2)) ∧
      (HSSym.decodeOutput n out).length ≤ s ^ (C * k ^ 2) ∧
      ∀ (F : Type) [Field F] [CharZero F],
        RatHits F (HSSym.decodeOutput n out) (InBorderSPS F n k s) := by sorry

end BorderDiffEq.Supplement
