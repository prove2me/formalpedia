-- Prove2me | Theorems.Thm_CVStabilizer_stabilizer_code_encodes
-- name    : CVStabilizer.stabilizer_code_encodes
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:21:06.524166+00:00
-- url     : https://prove2.me/theorems/94082b84-98e1-4634-9d00-b30141f55249
-- title:
--   $k$ symplectically orthogonal vectors give a stabilizer code whose logical operators form the Pauli group of $n-k$ modes
-- statement:
--   Let $u_1,\dots,u_k\in\mathbb R^{2n}$ be linearly independent with $\omega(u_i,u_j)=0$ for all $i,j$. Let $W=\operatorname{span}_{\mathbb R}\{u_i\}$, $W^\omega=\{v:\omega(v,u_i)=0\ \forall i\}$ and $S=\{U(w):w\in W\}$. Then:
--
--   1. **$S$ is a valid stabilizer:** $U(w)U(w')=U(w+w')$ for $w,w'\in W$, any two elements of $S$ commute, $U(0)=I$, $v\mapsto U(v)$ is one-to-one, and $-I\notin S$.
--   2. **Normalizer:** $U(v)$ commutes with all of $S$ iff $v\in W^\omega$, and $U(v)SU(v)^{-1}\subseteq S$ iff $v\in W^\omega$.
--   3. **Dimensions:** $k\le n$, $W\subseteq W^\omega$, $\dim W^\omega=2n-k$ and $\dim W^\omega/W=2(n-k)$.
--   4. **Logical basis:** there are $x_1,z_1,\dots,x_{n-k},z_{n-k}\in W^\omega$ with $\omega(x_i,x_j)=\omega(z_i,z_j)=0$ and $\omega(x_i,z_j)=\delta_{ij}$ whose classes form a basis of $W^\omega/W$.
--   5. **Logical Pauli group:** for all $i,j$ and real $s,t$,
--   $$
--   [U(s\,x_i),U(t\,x_j)]=[U(s\,z_i),U(t\,z_j)]=0,\qquad U(s\,x_i)U(t\,z_j)=e^{i\pi st\delta_{ij}}U(t\,z_j)U(s\,x_i),
--   $$
--   and $\varphi(a,b)=\sum_i(a_ix_i+b_iz_i)$ is an injective symplectic map $\mathbb R^{2(n-k)}\to\mathbb R^{2n}$ with $U(\varphi(\alpha))U(\varphi(\beta))=e^{i\pi\omega_{n-k}(\alpha,\beta)/2}U(\varphi(\alpha+\beta))$, $\varphi(e_i,0)=x_i$, $\varphi(0,e_i)=z_i$.
--
--   In the paper's words: "In brief, $k$ symplectically orthogonal vectors give rise to a continuous-variable code encoding $n-k$ continuous-variable systems." The statement is the content of the p.2 paragraphs that precede that sentence. The nontriviality of the code space is not part of it.
--
--   **Formalization Note** $U$ is the concrete realization $(U(s,t)\psi)(x)=e^{i\pi(\langle t,x\rangle+\langle s,t\rangle/2)}\psi(x+s)$ acting on all functions $\mathbb R^n\to\mathbb C$; operators are composed with $\circ$ and a scalar $c$ acts as $\psi\mapsto c\,\psi$.
--
--   Differences from the source:
--   - reading: U(v) = exp(iπ Σᵢ (sᵢp̂ᵢ + tᵢq̂ᵢ)) with [q̂, p̂] = 1 (2), which under no normalization of the canonical pair yields (3) as printed → the concrete realization weyl: (U(s,t)ψ)(x) = e^{iπ(⟨t,x⟩ + ⟨s,t⟩/2)} ψ(x + s); reason: (3), (7) and every example of the paper use (3); in this realization (3) and (7) hold verbatim, Z(t) = U(0,t) is the multiplication by e^{iπtx} of (11), X(s) = U(s,0) is the position shift ψ ↦ ψ(· + s), i.e. X(s)|q⟩ = |q − s⟩ (this direction is forced by (3) once Z(t) is the multiplication of (11); the p.3 example X̄(q)|000⟩ = |qqq⟩ reads the shift the other way, which is the paper's inconsistency, and no item depends on it), and the symmetric phase e^{iπ⟨s,t⟩/2} gives U(av)U(bv) = U((a+b)v)
--   - generalization: operators on the state space with position basis |q⟩ → operators on all functions ℝⁿ → ℂ; identities hold pointwise; reason: the position eigenvectors |q⟩ are not in L²; each U(v) is a shift followed by multiplication by a continuous phase, so it preserves L² and a.e. equality, every operator identity restricts to L²(ℝⁿ), and equality, commutation and injectivity of the U(v) are the same on L² as on all functions
--   - encoding: Gn = {X(s₁)Z(t₁) ⊗ ⋯ ⊗ X(sₙ)Z(tₙ)} (1), whose typical member is U(v) (2) → the Pauli operators are the U(v), v ∈ ℝ²ⁿ; global phases are not tracked; reason: X(s)Z(t) = e^{iπ⟨s,t⟩/2}U(s,t), and a scalar phase changes no commutation or conjugation statement
--   - generalization: S in one-to-one correspondence with the span W → v ↦ U(v) is injective on all of ℝ²ⁿ; reason: specializes to injectivity on W
--   - reading: k vectors u₁, …, u_k with ω(uᵢ, uⱼ) = 0, and dim W = k used in 'dim W^ω = dim ℝ²ⁿ − dim W = 2n − k' → LinearIndependent ℝ u; reason: the page uses dim W = k; without independence the claim fails (n = 1, k = 2, u₁ = u₂ = (1, 0): dim W^ω = 1 ≠ 0)
--   - encoding: W^ω = {v : ω(v, uᵢ) = 0 ∀i} → (omega n).orthogonal W = {v | ∀ w ∈ W, ω(w, v) = 0}; reason: equal sets, by antisymmetry and linearity of ω
--   - reading: 'the operators commuting with S, namely the normalizer N(S) of S' → both the commutant {v : U(v) commutes with S} and the normalizer {v : U(v)U(w)U(−v) ∈ S for all w ∈ W} are shown equal to W^ω; reason: the page identifies the two; stating both makes neither reading the weaker one
--   - encoding: n − k logical modes, 2n − k, 2(n − k) → k ≤ n is concluded; natural-number subtraction and index type Fin (n − k); reason: since k ≤ n is proved, the subtractions are the true differences
--   - encoding: a basis x₁, z₁, …, x_{n−k}, z_{n−k} ∈ ℝ²ⁿ for W^ω/W → xᵢ, zᵢ ∈ W^ω and the joint family (u, x, z) is linearly independent and spans W^ω; reason: equivalent to the classes of the xᵢ, zᵢ forming a basis of W^ω/W, without quotient types
--   - reading: U(s xᵢ)U(t zⱼ) = e^{iπstδᵢⱼ}U(t zⱼ), U(s xᵢ) (7), and [A, B] = 0 → U(s xᵢ) ∘ U(t zⱼ) = e^{iπstδᵢⱼ} • U(t zⱼ) ∘ U(s xᵢ); commutators as A ∘ B = B ∘ A; reason: the comma is a printing slip; with it removed (7) agrees with (3), since ω(s xᵢ, t zⱼ) = st δᵢⱼ
--   - reading: 'has the same group structure as the generalized Pauli group G_{n−k}, with U(s xᵢ) and U(s zᵢ) acting as position and momentum shifts on the i-th logical mode' → φ(a, b) = Σᵢ (aᵢxᵢ + bᵢzᵢ) is injective and symplectic, U(φ(α))U(φ(β)) = e^{iπω_{n−k}(α,β)/2} U(φ(α+β)), φ(eᵢ, 0) = xᵢ, φ(0, eᵢ) = zᵢ; reason: this is the precise content of the phrase: the logical operators obey the (n − k)-mode product law of the Weyl operators, with xᵢ, zᵢ the images of the i-th position and momentum directions
--   - reading: 'a continuous-variable code encoding n − k continuous-variable systems' (In brief, p.2) → clauses 1–5: N(S)/S ↔ W^ω/W of dimension 2(n − k) with the logical Pauli structure of G_{n−k}; no statement about the code space C(S) of (6); reason: the paper derives the encoding claim only through N(S)/S ≅ W^ω/W, the symplectic basis and (7); that C(S) is nontrivial is Gottesman's qubit fact carried over without argument ('The same fact is true in continuous dimensions'), and it is false in L²(ℝⁿ) (for (12), U(t u₁) is multiplication by e^{iπt(x₁−x₂)}, which fixes only ψ = 0), so a faithful version needs a distribution layer the paper does not specify
-- source:
--   Barnes, Stabilizer Codes for Continuous-variable Quantum Error Correction, arXiv:quant-ph/0405064v1, p.2, left column: "… and thus a valid stabilizer", the paragraph "Since any operator which commutes with everything in S…" through eq. (7), and "In brief, k symplectically orthogonal vectors give rise to a continuous-variable code encoding n −k continuous-variable systems"

import Mathlib
import Definitions.Def_CVStabilizer_Weyl

namespace CVStabilizer

/-- **k symplectically orthogonal vectors give a code encoding n − k modes**, Barnes,
arXiv:quant-ph/0405064v1, p.2: "In brief, k symplectically orthogonal vectors give rise to a
continuous-variable code encoding n − k continuous-variable systems", with the content of the
p.2 paragraphs that precede it. For linearly independent `u₁, …, u_k ∈ ℝ²ⁿ` with
`ω(uᵢ, uⱼ) = 0` for all `i, j`, `W = span_ℝ uᵢ`, `W^ω` its symplectic orthogonal and
`S = {U(w) : w ∈ W}`:

1. `S` is a valid stabilizer: closed under products (`U(w)U(w′) = U(w + w′)`), abelian,
   containing `I`, in one-to-one correspondence with `W`, not containing `−I`;
2. the commutant of `S` and the normalizer of `S` among the `U(v)` are both `{U(v) : v ∈ W^ω}`;
3. `k ≤ n`, `W ⊆ W^ω`, `dim W^ω = 2n − k`, `dim W^ω/W = 2(n − k)`;
4. there are `x₁, z₁, …, x_{n−k}, z_{n−k} ∈ W^ω` with `ω(xᵢ, xⱼ) = ω(zᵢ, zⱼ) = 0`,
   `ω(xᵢ, zⱼ) = δᵢⱼ`, whose classes form a basis of `W^ω/W`;
5. these satisfy (7), and `φ(a, b) = Σᵢ (aᵢxᵢ + bᵢzᵢ)` embeds `ℝ^{2(n−k)}` symplectically so that
   the logical operators `U(φ(α))` obey the product law of `G_{n−k}`, with `U(s xᵢ)`, `U(s zᵢ)`
   the position and momentum shifts of logical mode `i`.

**Formalization Note** `U` is the concrete realization `weyl` on all functions `ℝⁿ → ℂ`, in which
(3) and (7) hold as printed. Linear independence of the `uᵢ` is the page's implicit `dim W = k`.
`W^ω` is Mathlib's `(omega n).orthogonal W`, equal to `{v : ω(v, uᵢ) = 0 ∀i}` by antisymmetry.
The basis of `W^ω/W` is stated as "`(u, x, z)` is a basis of `W^ω`". Code-space nontriviality
is not part of this statement (see the mission description). -/
theorem stabilizer_code_encodes (n k : ℕ) (u : Fin k → PhaseSpace n)
    (hu : LinearIndependent ℝ u) (hiso : ∀ i j, omega n (u i) (u j) = 0) :
    let W : Submodule ℝ (PhaseSpace n) := Submodule.span ℝ (Set.range u)
    let Wω : Submodule ℝ (PhaseSpace n) := (omega n).orthogonal W
    ((∀ w ∈ W, ∀ w' ∈ W, weyl w ∘ weyl w' = weyl (w + w')) ∧
      (∀ w ∈ W, ∀ w' ∈ W, weyl w ∘ weyl w' = weyl w' ∘ weyl w) ∧
      weyl (0 : PhaseSpace n) = id ∧
      Function.Injective (weyl (n := n)) ∧
      (∀ w ∈ W, weyl w ≠ fun ψ => -ψ)) ∧
    (∀ v : PhaseSpace n, (∀ w ∈ W, weyl v ∘ weyl w = weyl w ∘ weyl v) ↔ v ∈ Wω) ∧
    (∀ v : PhaseSpace n,
      (∀ w ∈ W, ∃ w' ∈ W, weyl v ∘ weyl w ∘ weyl (-v) = weyl w') ↔ v ∈ Wω) ∧
    k ≤ n ∧ W ≤ Wω ∧ Module.finrank ℝ Wω = 2 * n - k ∧
    Module.finrank ℝ (Wω ⧸ W.comap Wω.subtype) = 2 * (n - k) ∧
    ∃ x z : Fin (n - k) → PhaseSpace n,
      (∀ i, x i ∈ Wω ∧ z i ∈ Wω) ∧
      (∀ i j, omega n (x i) (x j) = 0 ∧ omega n (z i) (z j) = 0 ∧
        omega n (x i) (z j) = if i = j then 1 else 0) ∧
      LinearIndependent ℝ (Sum.elim u (Sum.elim x z)) ∧
      Submodule.span ℝ (Set.range (Sum.elim u (Sum.elim x z))) = Wω ∧
      (∀ (i j : Fin (n - k)) (s t : ℝ),
        weyl (s • x i) ∘ weyl (t • x j) = weyl (t • x j) ∘ weyl (s • x i) ∧
        weyl (s • z i) ∘ weyl (t • z j) = weyl (t • z j) ∘ weyl (s • z i) ∧
        weyl (s • x i) ∘ weyl (t • z j) =
          (fun ψ => Complex.exp
              (((Real.pi * s * t * (if i = j then 1 else 0) : ℝ) : ℂ) * Complex.I) • ψ)
            ∘ weyl (t • z j) ∘ weyl (s • x i)) ∧
      (let φ : PhaseSpace (n - k) → PhaseSpace n := fun a => ∑ i, (a.1 i • x i + a.2 i • z i);
        Function.Injective φ ∧
        (∀ a b, omega n (φ a) (φ b) = omega (n - k) a b) ∧
        (∀ a b, weyl (φ a) ∘ weyl (φ b) =
          (fun ψ => Complex.exp (((Real.pi * omega (n - k) a b / 2 : ℝ) : ℂ) * Complex.I) • ψ)
            ∘ weyl (φ (a + b))) ∧
        (∀ i, φ (Pi.single i 1, 0) = x i ∧ φ (0, Pi.single i 1) = z i)) := by sorry

end CVStabilizer
