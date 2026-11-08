-- Prove2me | Theorems.Thm_AvoidPlast_theorem_4_5
-- name    : AvoidPlast.theorem_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:50:16.920404+00:00
-- url     : https://prove2.me/theorems/18177973-d668-4838-9d81-6291fb872a4e
-- title:
--   Theorem 4.5 — a PCPP for a zero-on-subcube test
-- statement:
--   Let $L$ be the pair language $\{((|F|,m,d,|H|),f):f\in\mathrm{ZoS}(F,m,d,H)\}$, with $f$ represented by a truth table, $H$ the first $|H|$ elements of $F$ and the integers in binary. Then for any $s\ge2^{-\mathrm{poly}(m,\log|F|)}$, $L\in\mathrm{PCPP}_{s,\delta}[r,q,t]$ with $\delta=1/\mathrm{poly}(m,\log|F|)$ and $r$, $q$, $t$ all $\mathrm{poly}(m,\log|F|)$. Moreover the verifier makes only non-adaptive queries, and the accepting proof can be deterministically computed in time $\mathrm{poly}(|F|^m)$ from the implicit input $f$.
--
--   **Formalization Note** The statement is for every field representation scheme.
--
--   Differences from the source:
--   - generalization: fields of characteristic 2 in the paper's use, with any reasonable ordering → every field representation scheme; reason: footnote 19 asks only for an enumerable order, and characteristic-2 fields numbered by their binary representations are a scheme
--   - reading: $\mathrm{PCPP}_{s,\delta}[r,q,t]$, not defined in this paper → the [BGH+05] class: a verifier with read-only tapes $x,\rho,y,\pi$; soundness for $y$ that is $\delta$-far; queries counted on $y$ and $\pi$; verification time on the machine; reason: the paper cites the class from [BGH+05] without defining it
--   - reading: proximity parameter $\delta=1/\mathrm{poly}(m,\log|F|)$ → $\delta=(m+\log_2(|F|+2))^{-b}$ for every $b$; reason: as in Theorem 4.2; the universal reading is the one the proof of Theorem 4.1 uses and the stronger one
--   - encoding: parameters as functions of $(m,\log|F|)$, on tuples → parameters read off the decoded tuple; a string that is no code gets error $0$ and $\mathrm{poly}(|x|)$ time; reason: a pair language must also reject malformed explicit inputs, and these carry no field
--   - encoding: the integers $|F|,m,d,|H|$ in binary → $d$ written last, most significant bit first; reason: so that verification time stays $\mathrm{poly}(m,\log|F|)$ for astronomically large $d$, as the printed bound requires
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 4.5, p.18

import Mathlib
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_HaltsWithin
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_Accepts
import Definitions.Def_AvoidPlast_lg
import Definitions.Def_AvoidPlast_IsPCPP
import Definitions.Def_AvoidPlast_FieldScheme
import Definitions.Def_AvoidPlast_encZoS
import Definitions.Def_AvoidPlast_decodeZoS
import Definitions.Def_AvoidPlast_zosLanguage

namespace AvoidPlast

/-- Theorem 4.5, a PCPP for a zero-on-subcube test (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.18), for every field representation
scheme and every `s ≥ 2^{-poly(m, log |F|)}`, with `δ = 1/poly(m, log |F|)`, `r`, `q` and `t` all
`poly(m, log |F|)`. Moreover the verifier is non-adaptive and an accepting proof is computed in time
`poly(|F|^m)` from the implicit input.

**Formalization Note** On a string that is not the code of a tuple, `x` carries no field, and there the
verifier must reject (error `0`) within `poly(|x|)` steps. `δ = (m + log₂(|F|+2))^{-b}` for every `b`,
as in `theorem_4_2`. -/
theorem theorem_4_5 (S : FieldScheme) (s : ℕ → ℕ → ℝ) (e : ℕ)
    (hs : ∀ Q m : ℕ, (2 : ℝ) ^ (-((e : ℝ) * ((m : ℝ) + lg Q) ^ e)) ≤ s Q m) (b : ℕ) :
    ∃ (a : ℕ) (V : Machine 4) (r q t : List Bool → ℕ → ℕ) (P : Machine 2),
      IsPCPP V (zosLanguage S)
        (fun x _ => match decodeZoS x with
          | some p => s p.1 p.2.1
          | none => 0)
        (fun x _ => match decodeZoS x with
          | some p => 1 / ((p.2.1 : ℝ) + lg p.1) ^ b
          | none => 0)
        r q t ∧
      (∀ (Q m d h K : ℕ), let x := encZoS Q m d h
        (r x K : ℝ) ≤ a * ((m : ℝ) + lg Q) ^ a ∧ (q x K : ℝ) ≤ a * ((m : ℝ) + lg Q) ^ a ∧
          (t x K : ℝ) ≤ a * ((m : ℝ) + lg Q) ^ a) ∧
      (∀ (x : List Bool) (K : ℕ), decodeZoS x = none →
        r x K ≤ a * (x.length + 1) ^ a ∧ q x K ≤ a * (x.length + 1) ^ a ∧
          t x K ≤ a * (x.length + 1) ^ a) ∧
      ∀ (Q m d h : ℕ) (f : List Bool), zosLanguage S (encZoS Q m d h) f →
        HaltsWithin P ![encZoS Q m d h, f] (a * (Q ^ m) ^ a) ∧
        ∀ ρ : List Bool, ρ.length = r (encZoS Q m d h) f.length →
          Accepts V ![encZoS Q m d h, ρ, f, output P ![encZoS Q m d h, f]] := by sorry

end AvoidPlast
