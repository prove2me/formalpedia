-- Prove2me | Theorems.Thm_DynOracleConn_lemma_3_2
-- name    : DynOracleConn.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:50:52.186642+00:00
-- url     : https://prove2.me/theorems/dce1db63-ef61-4409-a03b-0a6d2864466f
-- title:
--   Lemma 3.2, p.22 — $\mathbb P_X[H\ge h]\le2^B\binom Lh(d-h)!/d!$
-- statement:
--   Let an algorithm receive a $B$-bit advice string $\mathcal M(\pi,z)$ and make at most $L$ probes to the oracle $P_X$, where $X=(\pi,z)$. If $H$ is the number of distinct hits, then for every $h$,
--
--   $$\mathbb P_X[H\ge h]\le2^B\binom Lh\frac{(d-h)!}{d!}.$$
--
--   This bounds how many hits an algorithm can expect from few probes and little advice.
--
--   **Formalization Note** The probability is multiplied by the $d!\,2^d$ instances. The advice lies in a finite set of at most $2^B$ strings, and the algorithm is a probe tree per advice string, with the probe bound assumed on the run of each instance. For $h>d$ the count is $0$, so the natural-number subtraction in $(d-h)!$ does not matter.
--
--   Differences from the source:
--   - encoding: probability over uniform (π, z), blocks or offsets → a count of outcomes; reason: the outcome spaces are finite and uniform; same statement
--   - encoding: [d] 1-based → Fin d, 0-based; reason: Lean convention; same instances
--   - encoding: a B-bit string → a type Adv with at most 2^B elements; reason: same advice sets up to relabeling
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), Lemma 3.2, p.22

import Mathlib
import Definitions.Def_DynOracleConn_PPHP

namespace DynOracleConn

/-- **Lemma 3.2, p.22.** Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), Lemma 3.2, p.22: "Let 𝒜 be an algorithm that receives any B-bit
string 𝓜(π, z), and does at most L probes using the oracle P_X(·, ·) where X = (π, z), then
P_X[H ≥ h] ≤ 2^B · C(L, h) · (d − h)!/d!, where H is the number of distinct hits."

For an advice map `M` into a set of at most `2^B` strings and a probe tree `alg a` for each advice
`a` that makes at most `L` probes on every instance, the number of the `d!·2^d` instances `X` on
which the run has at least `h` distinct hits is at most `2^B · C(L, h) · (d − h)! · 2^d`.

**Formalization Note.** The probability over uniform `X = (π, z)` is written as a count
(multiplied by `d!·2^d`). `C(L, h)` is `Nat.choose`; for `h > d` the count is `0`. -/
theorem lemma_3_2 {d B L h : ℕ} {Adv R : Type} [Fintype Adv] (hAdv : Fintype.card Adv ≤ 2 ^ B)
    (M : PPHPInst d → Adv) (alg : Adv → PPHPTree d R)
    (hL : ∀ X : PPHPInst d, (alg (M X)).cost (pOracle X) ≤ L) :
    Set.ncard {X : PPHPInst d | h ≤ numHits (alg (M X)) X} ≤
      2 ^ B * L.choose h * (d - h).factorial * 2 ^ d := by sorry

end DynOracleConn
