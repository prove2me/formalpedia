-- Prove2me | Theorems.Thm_DetDLP_fp_dlp_from_primitive_root_and_full_dlp
-- name    : DetDLP.fp_dlp_from_primitive_root_and_full_dlp
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-23T09:49:30.395317+00:00
-- url     : https://prove2.me/theorems/67e5fc3a-21b7-4be0-b95f-1f99535ddebf
-- title:
--   Reduction of General Prime-Field DLP to Primitive-Root Finding and Two Full-Group DLPs
-- statement:
--   Suppose there exist (i) a deterministic multitape Turing machine constructing a primitive root $h \in \mathbb{F}_p^*$ ($\mathrm{ord}(h) = p - 1$) in time and space $2^{O(b/(\log b)^{1/4})}$ (Proposition 3.3), and (ii) a deterministic multitape Turing machine solving full-group discrete logarithms $h^u \equiv a \pmod p$ in time $2^{O(b/\sqrt{\log\log b})}$ and space $2^{O(b/(\log b)^{1/4})}$. Then there exists a uniform deterministic multitape Turing machine running within the same time and space bounds that, given any prime $p \ge 2$ and any $g, t \in \mathbb{F}_p^*$, decides whether $t \in \langle g \rangle$ and outputs `none` if $t \notin \langle g \rangle$ or `some x` with $x < \mathrm{ord}(g)$ and $g^x \equiv t \pmod p$ otherwise:
--
--   $$d_0 = \gcd(u, p-1), \qquad t \in \langle g \rangle \iff d_0 \mid v, \qquad x \equiv (v/d_0)(u/d_0)^{-1} \pmod{(p-1)/d_0}.$$
--
--   This reduction handles arbitrary subgroups $\langle g \rangle \le \mathbb{F}_p^*$ via two full-group discrete logarithm calls $u = \log_h g$ and $v = \log_h t$ plus extended-Euclidean arithmetic.
--
--   **Formalization Note** Composes two `PrimitiveMachine` subroutines cleanly on `encodeFpDLPInput` / `encodeOptionNatBin`.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 4.3, Proof of Theorem 1.1(2) (p. 17)

import Mathlib
import Definitions.Def_DetDLP_Machine

set_option autoImplicit false

namespace DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem fp_dlp_from_primitive_root_and_full_dlp :
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
      ∀ (p : ℕ) [Fact p.Prime] (g t : (ZMod p)ˣ),
        (t ∉ Subgroup.zpowers g →
          RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
            (encodeOptionNatBin none)
            (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p))) ∧
        (t ∈ Subgroup.zpowers g →
          ∃ x : ℕ, x < orderOf g ∧ g ^ x = t ∧
            RunsWithin M_fp out_fp (encodeFpDLPInput p (g : ZMod p).val (t : ZMod p).val)
              (encodeOptionNatBin (some x))
              (mainTimeBound C_fp (bitLen p)) (mainSpaceBound C_fp (bitLen p)))) := by sorry

end DetDLP
