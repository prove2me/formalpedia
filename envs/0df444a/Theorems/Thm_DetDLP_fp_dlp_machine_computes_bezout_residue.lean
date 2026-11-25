-- Prove2me | Theorems.Thm_DetDLP_fp_dlp_machine_computes_bezout_residue
-- name    : DetDLP.fp_dlp_machine_computes_bezout_residue
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T10:01:31.664992+00:00
-- url     : https://prove2.me/theorems/9fbaec7c-20f2-4e9d-a3d7-4c0588a1f2b2
-- title:
--   Prime-field DLP machine composition for the Bézout residue
-- statement:
--   Assume uniform deterministic multitape Turing machines for finding a primitive root $h$ in $\mathbb{F}_p^\times$ and for computing the full-group logarithm of any unit to base $h$, within the bounds in Proposition 3.3 and Theorem 1.1.
--
--   Let $p$ be prime and let $g,t$ be units in $\mathbb{F}_p$. Write $n=p-1$ and let $u,v\in[0,n)$ satisfy $h^u=g$ and $h^v=t$ for a primitive root $h$. Define $d=\gcd(u,n)$ and let $a$ be the coefficient of $u$ returned by the extended Euclidean algorithm, so that $au+bn=d$ for an integer $b$. Then there is a uniform deterministic multitape Turing machine that, on the encoded input $(p,g,t)$, outputs
--   $$
--   \begin{cases}
--   \texttt{some}(a(v/d)\bmod (n/d)) & d\mid v,\\
--   \texttt{none} & d\nmid v.
--   \end{cases}
--   $$
--   Here the remainder is the least nonnegative residue. The time bound is $\texttt{mainTimeBound}(C,\lceil\log_2 p\rceil)$ and the space bound is $\texttt{mainSpaceBound}(C,\lceil\log_2 p\rceil)$ for a uniform constant $C$.
--
--   The specification isolates the composition of the primitive-root and full-group logarithm subroutines with extended-Euclidean arithmetic and the required binary output encoding.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.3, Proof of Theorem 1.1(2), p. 17. Machine composition isolated from DetDLP.fp_dlp_from_primitive_root_and_full_dlp.

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem fp_dlp_machine_computes_bezout_residue :
    (∃ (M_pr : PrimitiveMachine) (out_pr : Fin M_pr.tapeCount) (C_pr : ℕ),
      ∀ (p : ℕ) [Fact p.Prime],
        ∃ h : (ZMod p)ˣ,
          orderOf h = p - 1 ∧
          RunsWithin M_pr out_pr (countWord p) (countWord (h : ZMod p).val)
            (mainSpaceBound C_pr (bitLen p)) (mainSpaceBound C_pr (bitLen p))) →
    (∃ (M_full : PrimitiveMachine) (out_full : Fin M_full.tapeCount) (C_full : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h a : (ZMod p)ˣ),
        orderOf h = p - 1 →
        ∃ u : ℕ, u < p - 1 ∧ h ^ u = a ∧
          RunsWithin M_full out_full (encodeFpDLPInput p (h : ZMod p).val (a : ZMod p).val)
            (countWord u)
            (mainTimeBound C_full (bitLen p)) (mainSpaceBound C_full (bitLen p))) →
    (∃ (M_fp : PrimitiveMachine) (out_fp : Fin M_fp.tapeCount) (C_fp : ℕ),
      ∀ (p : ℕ) [Fact p.Prime] (h g t : (ZMod p)ˣ) (u v : ℕ),
        orderOf h = p - 1 → u < p - 1 → v < p - 1 → h ^ u = g → h ^ v = t →
        let n := p - 1
        let d := Nat.gcd u n
        let x := ((Nat.gcdA u n * (v / d : ℕ)) % ((n / d : ℕ) : ℤ)).toNat
        RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
          (encodeOptionNatBin (if d ∣ v then some x else none))
          (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p))) := by sorry

end DetDLP
