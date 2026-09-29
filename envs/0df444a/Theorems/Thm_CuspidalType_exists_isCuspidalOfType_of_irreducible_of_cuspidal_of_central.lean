-- Prove2me | Theorems.Thm_CuspidalType_exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central
-- name    : CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/5cf2dbb6-37d0-5560-88dd-46cbc68bebfc
-- title:
--   Irreducible cuspidal representations of GL₂(𝔽_q) have a type
-- statement:
--   Let $q$ be a prime, let $K$ be an algebraically closed field of characteristic zero, and let $V$ be a non-zero finite-dimensional $K$-vector space carrying a representation $\rho$ of `GL2 q`, the group of invertible $2\times 2$ matrices over $\mathbb{Z}/q$. Three hypotheses are imposed: $\rho$ is irreducible, in the sense that every subrepresentation whose underlying submodule is non-zero has underlying submodule all of $V$; $\rho$ is cuspidal, in the sense that any $v \in V$ fixed by $\rho(\mathrm{unipotent}(t))$ for every $t \in \mathbb{Z}/q$, where $\mathrm{unipotent}(t)$ is the matrix $\begin{pmatrix}1&t\\0&1\end{pmatrix}$, is zero; and $\rho$ has trivial central character, in the sense that $\rho(\mathrm{scalarElem}(c)) = \mathrm{id}_V$ for every unit $c$ of $\mathbb{Z}/q$, where $\mathrm{scalarElem}(c)$ is the scalar matrix $c \cdot 1$. The conclusion is that there exists a group homomorphism $\theta \colon (\mathbb{F}_{q^2})^\times \to K^\times$, from the units of `GaloisField q 2`, such that `IsCuspidalOfType θ ρ` holds, i.e. $\dim_K V = q - 1$ (truncated subtraction of naturals), the cuspidality and triviality-of-central-character conditions above hold, and for every $\alpha \in (\mathbb{F}_{q^2})^\times$ one has $$\mathrm{charpoly}\bigl(\rho(\mathrm{torus}(\alpha))\bigr)\cdot \bigl(X - \theta(\alpha)\bigr)\bigl(X - \theta(\alpha)^{-1}\bigr) = \mathrm{charpoly}\bigl(\mathrm{ind}\,q\,K\,(\mathrm{torus}(\alpha))\bigr),$$ where $\mathrm{torus}$ embeds $(\mathbb{F}_{q^2})^\times$ into `GL2 q` by multiplication on $\mathbb{F}_{q^2}$ read in the basis `quadBasis q`, and `ind q K` is the comparison representation of `GL2 q` over $K$ used in the definition of a cuspidal type.
--
--   This is the existence half of the classification of the irreducible cuspidal representations of $\mathrm{GL}_2(\mathbb{F}_q)$ with trivial central character: each such representation has dimension $q-1$ and is attached to a character $\theta$ of the non-split torus $(\mathbb{F}_{q^2})^\times$. It is used when the mod-$q$ (or $q$-adic) representation attached to a newform is analysed locally at $q$, to produce the type $\theta$ of the local cuspidal constituent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central.lean

import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CuspidalType

theorem CuspidalType.exists_isCuspidalOfType_of_irreducible_of_cuspidal_of_central
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hirr : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ → W.toSubmodule = ⊤)
    (hcusp : ∀ v : V, (∀ t : ZMod q, ρ (unipotent q t) v = v) → v = 0)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id) :
    ∃ θ : (GaloisField q 2)ˣ →* Kˣ, IsCuspidalOfType θ ρ := by sorry
