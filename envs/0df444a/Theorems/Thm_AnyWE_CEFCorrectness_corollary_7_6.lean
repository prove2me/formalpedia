-- Prove2me | Theorems.Thm_AnyWE_CEFCorrectness_corollary_7_6
-- name    : AnyWE.CEFCorrectness.corollary_7_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:54:18.117638+00:00
-- url     : https://prove2.me/theorems/9a8df90d-7b4f-49a8-a828-db06b592f8ed
-- title:
--   Corollary 7.6 (= Theorem 1.3) — the transformed witness encryption $\mathrm{WE}'$ has $\ell$-CEF proofs of correctness for every constant $\ell\ge1$, in both forms
-- statement:
--   Let $n(\lambda),m(\lambda)$ be polynomial instance and witness lengths and let $R$ be an NP relation given by well-formed relation circuits $C_\lambda$ on $n(\lambda)+m(\lambda)$ inputs of polynomial size. Let $\mathrm{Com}$ be a computationally hiding, statistically binding bit commitment scheme in the CRS model (Definition 4.3), $G$ a polynomially secure length-doubling PRG, $\mathrm{NIWI}$ a statistically sound, witness-indistinguishable NIWI for the relation $R^\vee_{\mathrm{gate}}$ of Algorithm 1 (Definition 4.14), and $\mathrm{WE}$ a statistically correct, semantically secure witness encryption scheme for $R_{\mathrm{NIZK}}$ (Definition 4.16). Let $\mathrm{WE}'$ be the scheme of Algorithm 3 built from them, with witness bound $N=m$. Then for every bound $k\ge2$ on the premises of Logical Inference and every constant $\ell\ge1$:
--
--   1. there are polynomials $t,s$ such that for every instance family $\{x_\lambda\}$ and every bit $b$ the assertion family
--   $$R(x_\lambda,w)=1\ \Longrightarrow\ \mathrm{WE}'.\mathrm{Dec}\big(\mathrm{WE}'.\mathrm{Enc}(x_\lambda,b;r_1),w;r_2\big)=b$$
--   admits a $(t,s,\ell)$-CEF proof (Definition 7.2); **and**
--   2. there are polynomials $t,s$ such that for every instance family and every bit the two correctness samplers of Definition 7.3 admit a $(t,t,s,\ell)$-CEF proof of indistinguishability.
--
--   This is the paper's announced result "cryptographic proofs of correctness are free": any witness encryption scheme, used as a black box, becomes one with short CEF proofs of correctness, assuming one-way functions (which give $\mathrm{Com}$ and $G$) and statistically sound NIWIs. It is the step through which the paper obtains SNARGs from LWE and witness encryption.
--
--   Differences from the source:
--   - generalization: under the assumptions of Theorem 7.4 (one-way functions, statistically correct WE for NP, statistically sound NIWIs for NP) → for every commitment scheme (Definition 4.3), length-doubling PRG, NIWI for R∨gate (Definition 4.14) and statistically correct WE for R_NIZK (Definition 4.16); reason: the proof uses only these properties; the paper's instantiation from one-way functions (Theorem 4.4, [HILL99]) and from schemes for NP is a special case.
--   - generalization: an NP relation given by a Turing machine with polynomial clock, algorithms as polynomial-time machines, primitives for all lengths → relation and algorithms as polynomial-size circuit families at the lengths at which they are used (instance and witness lengths n(λ), m(λ); NIWI at R∨gate's lengths, WE at R_NIZK's); reason: unrolling a polynomial-time machine (Remark 4.2) gives such circuits, and a scheme for all lengths restricts to these lengths, so the paper's statement is a special case.
--   - encoding: the circuits of WE′.Enc and WE′.Dec as the unrolling of the machines of Algorithm 3 → the composition of the circuits of their parts; reason: the paper identifies hardwired templates and universal-circuit evaluation with the direct computation (p. 41); the two differ by polynomial-size EF equivalences.
--   - reading: the NIWI's completeness, soundness and witness indistinguishability for "R∨gate", a relation hardwiring the sampled crs_Com → negligible errors and the WI bound uniform over crs_Com; reason: NIWI.Gen receives R∨gate as input, and the paper's proof (union bound over gates, reductions fixing crs_Com) uses this uniformity.
--   - reading: Com.Gen "outputs a uniformly random public reference string" → the reference string is Com.Gen's random tape; reason: the plain reading of "uniformly random reference string".
--   - encoding: the fixed-length specialization N = n_w of Algorithm 1 → no witness-length, N or setup-parameter fields in the CRS, proofs and gate instances; no malformed-encoding checks; the NIZK prover omits its own R-check (WE′.Dec checks R first); one opening per wire in the prover's tape (unused for public wires); reason: at fixed lengths these fields are constants and these checks always pass.
--   - encoding: outputs in {0, 1, ⊥} → two bits (valid, bit), ⊥ = (0, 0), with WE.Dec's output (0, ·) read as ⊥; reason: Definition 7.3 asks for one binary encoding of 0, 1, ⊥ in both circuits.
--   - reading: "a constant number of formulas" in Logical Inference → at most k premises, for every k ≥ 2; reason: a constant fixed before the proof; for k ≥ 2 the systems agree up to polynomial factors, absorbed by the existential t, s.
--   - reading: Extension "e an extension variable" → e does not occur in Φ_{i−1} or in ψ; reason: §4.1.1 requires fresh extension variables; the stricter system makes the conclusion stronger.
--   - encoding: a sampled circuit with key hardwired, whose description distinguishers receive → a fixed template with the key as data, distinguishers receive (aux, key), output steps require equal templates; reason: the paper's convention before Theorem 5.6.
--   - encoding: gate equations {out := C(in)} → one equation per gate plus one per output, hardwired bits as ⊤/⊥, = and ↔ identified, |C| = number of gates; reason: Lean representation of Definition 4.25.
--   - encoding: the standard tableau circuit C_{R,n,m} of R → a relation circuit family that is well-formed (every gate reads earlier wires, every output is a wire); reason: unrolling a machine yields such a circuit, and well-formedness excludes no relation, only circuits with dangling references.
--   - encoding: Definition 7.3's samplers output (ct, C_{x,ct}) and (ct, D_{x,b}) → both generators output (aux, key) = (ct, ct); D_{x,b} carries ct as an unused key and has an empty evaluation tape; reason: distinguishers receive the same information (ct), and D_{x,b} computes the same function.
--   - encoding: polynomial lengths n, m and polynomials t, s → `IsPoly` / `Polynomial ℕ` evaluated at λ; the CEF sequence length is exactly u(λ) for a polynomial u; reason: standard reading of Definitions 4.29, 7.2 and 7.3.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), p. 64, Corollary 7.6 (informal Theorem 1.3, p. 3)

import Mathlib
import Definitions.Def_AnyWE_CEFCorrectness_WEPrime
import Definitions.Def_AnyWE_CEFCorrectness_CorrectnessProofs
set_option autoImplicit false

namespace AnyWE.CEFCorrectness

open GateNIZK Correctness

/-- **Corollary 7.6** (p. 64; formal Theorem 1.3). For every NP relation given by polynomial-size
well-formed relation circuits `RC` at polynomial instance and witness lengths `n, m`, every
commitment scheme `Com` (Definition 4.3), length-doubling PRG `G`, NIWI for `R^∨_gate`
(Definition 4.14) and statistically correct witness encryption `WE` for `R_NIZK`
(Definition 4.16), every premise bound `k ≥ 2` and every constant `ℓ ≥ 1`, the scheme `WE′` of
Algorithm 3 (witness bound `N = m`) has `ℓ`-CEF proofs of correctness in the sense of
Definition 7.2 **and** in circuit-sampler form (Definition 7.3). -/
theorem corollary_7_6 (n m : ℕ → ℕ) (hn : IsPoly n) (hm : IsPoly m)
    (RC : ∀ lam, Circuit (n lam + m lam) 1) (hRC_wf : ∀ lam, (RC lam).WF)
    (hRC_poly : PolyFamily (a := fun lam => n lam + m lam) (b := fun _ => 1) RC)
    (Com : Commitment) (hCom : Com.IsCommitment) (G : PRG) (hG : G.IsSecure)
    (NIWI : NIWIScheme (orGateRel n m RC Com G)) (hNIWI : NIWI.IsNIWI)
    (WE : WEScheme (nizkRel n m RC Com G NIWI)) (hWE : WE.IsWE)
    (k : ℕ) (hk : 2 ≤ k) (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    HasLCEFProofs RC (WEPrime.scheme n m RC Com G NIWI WE) k (fun _ => ℓ) ∧
      HasLSamplerCEFProofs RC (WEPrime.scheme n m RC Com G NIWI WE) k (fun _ => ℓ) := by sorry

end AnyWE.CEFCorrectness
