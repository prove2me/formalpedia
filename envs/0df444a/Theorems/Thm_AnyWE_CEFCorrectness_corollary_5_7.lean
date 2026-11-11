-- Prove2me | Theorems.Thm_AnyWE_CEFCorrectness_corollary_5_7
-- name    : AnyWE.CEFCorrectness.corollary_5_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:53:02.93622+00:00
-- url     : https://prove2.me/theorems/5d460744-78b7-4eb4-b2b5-712d4d1517c3
-- title:
--   Corollary 5.7 — CEF proofs of indistinguishability with an endpoint EF proof give $(t',s',\ell)$-CEF proofs of correctness for $\ell=O(\log\lambda)$
-- statement:
--   Fix a bound $k\ge2$ on the premises of Logical Inference. There is a fixed polynomial $p$ such that the following holds. Let $m,t,s,q$ be polynomials in $\lambda$ and $\ell=O(\log\lambda)$, and let $\mathrm{Gen}^{(0)},\mathrm{Gen}^{(1)}$ be circuit samplers with polynomial input length $n=n(\lambda)$ that admit an $(m,t,s,\ell)$-CEF proof of indistinguishability (Definition 5.4). Let $F=\{F_\lambda\}$ be deterministic circuits on $n(\lambda)$ bits with the samplers' output length, and suppose that for every $\lambda$ the endpoint assertion $D_k(x;r)=F_\lambda(x)$, $(\mathrm{aux},D_k)\leftarrow\mathrm{Gen}^{(1)}(1^\lambda;\rho)$, has an EF proof of length at most $q(\lambda)$. Then the correctness assertion of Theorem 5.6 for $\mathrm{Gen}^{(0)}$ and $F$ admits a $(t',s',\ell)$-CEF proof, where
--   $$\sigma=\max\{s,2^\ell\},\qquad t'=p(t+q+n+|F|)\cdot\sigma^2,\qquad s'=p(t+q+n+|F|)\cdot\sigma .$$
--   Since $\ell=O(\log\lambda)$, both are polynomial when $|F|$ is.
--
--   This is the form in which the transfer principle is applied to the circuit samplers of witness encryption: it turns Definition 7.3 into Definition 7.2.
--
--   Differences from the source:
--   - reading: "for the fixed polynomial p of Theorem 5.6" → there is a fixed polynomial p (for each k) for which the corollary holds; reason: p is existential in both results, and linking it to the polynomial of a separate item would require restating Theorem 5.6 as a hypothesis.
--   - reading: "a constant number of formulas θ1, …, θc" in Logical Inference → at most k premises, for every k ≥ 2, with p chosen after k; reason: a constant fixed before the proof; for k ≥ 2 the systems agree up to polynomial factors.
--   - reading: Extension "e an extension variable" → e does not occur in Φ_{i−1} or in ψ; reason: §4.1.1 requires extension variables to be fresh.
--   - encoding: a sampled circuit with key k hardwired, whose description the distinguisher receives → a fixed template with the key k as data; the distinguisher receives (aux, k), and an output step requires equal templates; reason: the paper's convention before Theorem 5.6; template changes go through EF equivalences.
--   - reading: "EF proofs establishing aux^(b) = aux′, C^(b)(x; r) = D^(b)(x; r)" → one EF proof per b of both equalities; reason: the two equalities are listed as one assertion per b.
--   - encoding: gate equations {out := C(in)} → one equation per gate plus one per output, hardwired bits as ⊤/⊥, = and ↔ identified, |C| = number of gates; reason: Lean representation of Definition 4.25.
--   - encoding: polynomials in λ, ℓ = O(log λ) → `Polynomial ℕ` evaluated at λ; ℓ(λ) ≤ C·⌊log₂ λ⌋ for a constant C and all large λ; reason: standard readings; the CEF sequence length is exactly u(λ) for a polynomial u as in Definition 4.29.
--   - encoding: the total encoding length of Definition 5.3 and the description length and running time of Gen′ in Definition 5.2 → the sum, over the generator and template of every sampler and every gadget circuit, of inputs + outputs + gates, plus the lengths of the supplied EF proofs; reason: polynomially related to a bit encoding of the same circuits, and the fixed polynomial p absorbs polynomial changes of t.
-- source:
--   Jain, Jin, Mathialagan, SNARGs from any Witness Encryption, and More, STOC 2027 submission (manuscript sha256 9bc2f227…), p. 44, Corollary 5.7

import Mathlib
import Definitions.Def_AnyWE_CEFCorrectness_Sampler
set_option autoImplicit false

namespace AnyWE.CEFCorrectness

/-- **Corollary 5.7** (p. 44). For every premise bound `k ≥ 2` there is a fixed polynomial `p`
such that: if `m, t, s, q` are polynomials, `ℓ = O(log λ)`, the circuit samplers
`Gen^(0), Gen^(1)` (polynomial input length `n`) admit an `(m, t, s, ℓ)`-CEF proof of
indistinguishability, and for every `λ` the endpoint assertion for `Gen^(1)` and the deterministic
circuit `F_λ` has an EF proof of length at most `q(λ)`, then the correctness assertion family for
`Gen^(0)` admits a `(t', s', ℓ)`-CEF proof with `σ = max{s, 2^ℓ}`,
`t' = p(t + q + n + |F|)·σ²`, `s' = p(t + q + n + |F|)·σ`. -/
theorem corollary_5_7 (k : ℕ) (hk : 2 ≤ k) :
    ∃ p : Polynomial ℕ, ∀ (mP tP sP qP : Polynomial ℕ) (ℓ : ℕ → ℕ), IsOLog ℓ →
      ∀ (n a o : ℕ → ℕ), IsPoly n →
      ∀ (Gen₀ Gen₁ : ∀ lam, SamplerAt (n lam) (a lam) (o lam)),
        CEFIndist k (fun lam => mP.eval lam) (fun lam => tP.eval lam) (fun lam => sP.eval lam) ℓ
          Gen₀ Gen₁ →
      ∀ (F : ∀ lam, Circuit (n lam) (o lam)) (efp : ∀ lam, List (Finset Formula)),
        (∀ lam, IsEFProof k ((Gen₁ lam).corrAssertion (F lam) .proper) (efp lam) ∧
          derivLength (efp lam) ≤ qP.eval lam) →
        CEFProof k
          (fun lam => p.eval (tP.eval lam + qP.eval lam + n lam + (F lam).size) *
            (max (sP.eval lam) (2 ^ ℓ lam)) ^ 2)
          (fun lam => p.eval (tP.eval lam + qP.eval lam + n lam + (F lam).size) *
            max (sP.eval lam) (2 ^ ℓ lam))
          ℓ (fun lam => (Gen₀ lam).corrAssertion (F lam) .random) := by sorry

end AnyWE.CEFCorrectness
