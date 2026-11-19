-- Prove2me | Theorems.Thm_APSCounting893_Main_bounded_least_witness_graph_in_ch
-- name    : APSCounting893.Main.bounded_least_witness_graph_in_ch
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T22:12:42.611194+00:00
-- url     : https://prove2.me/theorems/33abe60c-9b29-4350-a0d3-2a8dcd88a669
-- title:
--   Bounded least-witness value graphs stay in CH
-- statement:
--   Let $A$ be a language at counting level $j$. For fixed natural numbers $a,b$, let $\mu_{A,a,b}(x)$ be the least natural number $n<2^{a(|x|+1)^b}$ whose framed binary query belongs to $A$, or zero if no such number exists. Then
--   $$\operatorname{Graph}(\mu_{A,a,b})\in C_{j+8}P.$$
--   The assertion uses actual uniform finite oracle machines. The relative hierarchy overhead and all resource constants are independent of the input word. This bounded-search closure supplies least generators and discrete logarithms for the implicit CRT arithmetic stage.
-- source:
--   Bounded-search implementation for the discrete logarithms and primitive generators in Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, Section 4, Steps 2–3 and Lemmas 4.1–4.3, pp. 9–11, https://www.cs.rutgers.edu/~allender/papers/division.pdf. Used in the finite-machine arithmetic foundations for Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4.

import Definitions.Def_APSCounting893_Main_BoundedLeastArithmetic
set_option autoImplicit false
open APSCounting893.Main

theorem APSCounting893.Main.bounded_least_witness_graph_in_ch (A : Language) (j a b : ℕ)
    (hA : AtCHLevel j A) :
    AtCHLevel (j+8) (NaturalGraphLanguage (boundedLeastValue A a b)) := by sorry
