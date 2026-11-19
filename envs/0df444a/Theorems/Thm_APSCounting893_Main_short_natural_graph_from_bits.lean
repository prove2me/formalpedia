-- Prove2me | Theorems.Thm_APSCounting893_Main_short_natural_graph_from_bits
-- name    : APSCounting893.Main.short_natural_graph_from_bits
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T20:47:21.129198+00:00
-- url     : https://prove2.me/theorems/32e4b351-1507-4099-b717-88ef5d203a15
-- title:
--   Recovering a polynomial-length value from its CH bit language
-- statement:
--   Let $F$ assign a natural number to each binary input word, and suppose fixed natural numbers $a,b$ bound its binary length on every input:
--   $$\operatorname{bits}(F(x))\le a(|x|+1)^b.$$
--   If the bit-query language of $F$ belongs to counting level $j$, then its value-graph language belongs to level $j+3$:
--   $$\operatorname{BIT}_F\in C_jP\quad\Longrightarrow\quad\operatorname{GRAPH}_F\in C_{j+3}P.$$
--   A graph query consists of a framed input word followed by arbitrary little-endian candidate bits. All such words, including candidates with trailing zeros, are covered.
--
--   This is an implicit short-value interface for arithmetic constructions: a bounded-length integer can be tested through its individual bits while retaining a fixed counting level. The hierarchy uses the published physical finite oracle machines.
-- source:
--   Finite-machine bit-to-value interface used for the short-integer operations in Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, Section 4, pp. 8–11 of the author manuscript, https://www.cs.rutgers.edu/~allender/papers/division.pdf; arithmetic-to-threshold construction used in Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf. The explicit overhead of three levels reflects the published native preprocessing and bounded-universal simulation interfaces.

import Definitions.Def_APSCounting893_Main_BinaryOracleArithmetic
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.short_natural_graph_from_bits
    (F : Word → ℕ) (j a b : ℕ)
    (hF : ∀ x,(F x).bits.length ≤ polyBound a b x.length)
    (hbits : AtCHLevel j (NaturalBitLanguage F)) :
    AtCHLevel (j+3) (NaturalGraphLanguage F) := by sorry
