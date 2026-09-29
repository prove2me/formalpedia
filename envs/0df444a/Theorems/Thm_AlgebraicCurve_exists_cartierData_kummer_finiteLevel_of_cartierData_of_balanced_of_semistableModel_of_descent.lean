-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent
-- name    : AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/75cc50a6-fbfc-5f57-b3ab-17263341a9ae
-- title:
--   Descent of Cartier–Kummer data to a finite henselian level
-- statement:
--   Throughout, a `Place L F` is a valuation subring of $F$ containing the image of $L$, different from $F$ and a principal ideal ring; `ord` denotes minus the logarithm of the associated rank-one valuation, `evalAt` the residue map composed with the inverse of $L \to$ residue field (and $0$ off the valuation ring), and a place is rational when $L$ surjects onto its residue field. A `Divisor L F` is a finitely supported $\mathbb{Z}$-valued function on places, and `genusFF` is the dimension over the base field of $H^1$ of the zero divisor.
--
--   **Base and curve.** Let $L$ be an algebraically closed field, $A \subseteq L$ a valuation subring, $\pi \in A$ a nonzero element of the maximal ideal, and assume `hrk`: for every $x \in L$, $x \ne 0$, and every $y$ in the maximal ideal of $A$ there is $n \in \mathbb{N}$ with $v_A(y^n) \le v_A(x)$. Let $F$ be a field extension of $L$ which is a curve over $L$ in the sense of `IsCurveOver` (principal divisors, finite residue extensions, and $\Omega_{F/L}$ free of rank one) and essentially of finite type over $L$.
--
--   **Charts, annuli and their combinatorics.** Let $\iota V, \iota E$ be finite index types and, for each $i \in \iota V$, let $\bar F_i$ be a field over $\kappa :=$ the residue field of $A$, a curve over $\kappa$ and essentially of finite type over it, such that (`hratBar`) all places of $\bar F_i/\kappa$ are rational. For each $i$ let $C_i$ be a `ComponentChart`: a valuation subring $(C_i).\mathrm{integers}$ of $F$, a surjective ring map $(C_i).\mathrm{residue}$ onto $\bar F_i$ with kernel the maximal ideal, a set $(C_i).\mathrm{dom}$ of places of $F/L$, a finite set $(C_i).\mathrm{nodes}$ of places of $\bar F_i/\kappa$, a map $(C_i).\mathrm{placeMap}$ on places, together with the compatibility axioms of that structure; assume (`hratF`) every place in $(C_i).\mathrm{dom}$ is rational. Let $An, An' : \iota E \to \mathrm{Annulus}\,A\,F$ (each consisting of a set of places, a parameter in $F$, a modulus in the maximal ideal of $A$, and the axioms of that structure), let $\mathrm{src}, \mathrm{tgt} : \iota E \to \iota V$, let $x_s(e)$, $x_t(e)$ be places of $\bar F_{\mathrm{src}(e)}$, resp. $\bar F_{\mathrm{tgt}(e)}$, and let $w : \iota E \to \mathbb{N}$. The hypotheses are: `hpair`, that for each $e$ the annuli $An'\,e$ and $An\,e$ have the same domain and the same modulus, that this modulus is nonzero in $L$, and that the product of the two parameters is the image of the modulus in $F$; `hw`, that the modulus of $An\,e$ is a unit of $A$ times $\pi^{w(e)}$; `hatt`, that $An\,e$ is attached to $C_{\mathrm{src}(e)}$ at $x_s(e)$ and $An'\,e$ to $C_{\mathrm{tgt}(e)}$ at $x_t(e)$, attachment meaning that the place is a node of the chart, that the annulus parameter lies in the chart's integers with residue of order $1$ at that node, and that for every $f$ in the chart's integers with nonzero residue and $\mathrm{ord}_P f = 0$ on the annulus domain, $\mathrm{evalAt}_P(f) \cdot \mathrm{evalAt}_P(\text{param})^{-\mathrm{ord}_x(\text{residue } f)}$ lies in $A$ and is a unit there, for all $P$ in the annulus domain; `hnodes`, two clauses asserting that every node of every chart occurs as an endpoint $(\mathrm{src}\,e, x_s(e))$ or $(\mathrm{tgt}\,e, x_t(e))$, and that such an occurrence is unique as an element of $\iota E \sqcup \iota E$; `hcover`, that every place of $F/L$ either lies in exactly one chart domain and in no annulus domain, or lies in exactly one annulus domain and in no chart domain; `hdisc`, that for each $i$ and each place $Q$ of $\bar F_i/\kappa$ which is not a node there is $T$ in $(C_i).\mathrm{integers}$ whose residue is nonzero and has order $1$ at $Q$, such that every $P \in (C_i).\mathrm{dom}$ with $(C_i).\mathrm{placeMap}\,P = Q$ has $T$ in its valuation ring with $\mathrm{evalAt}_P(T)$ in the maximal ideal of $A$, and such that for every $c$ in the maximal ideal of $A$ there is exactly one $P \in (C_i).\mathrm{dom}$ above $Q$ with $\mathrm{evalAt}_P(T) = c$; and `hgenus`, the numerical identity $\mathrm{genus}(F/L) + \#\iota V = \sum_i \mathrm{genus}(\bar F_i/\kappa) + \#\iota E + 1$.
--
--   **Model and descent.** Let $M$ be a `SemistableModel` for these data: an integral scheme $M.X$, proper, flat and locally of finite presentation over $\mathrm{Spec}\,A$, an isomorphism $M.\mathrm{ffEquiv} : F \cong K(M.X)$ compatible with $A$, points $M.\mathrm{pt}\,P$, $M.\mathrm{gen}\,i$ and the remaining points of the structure realising the places, the chart generic points, the smooth chart points and the nodes, with the stated identifications of local rings and specialisations. Let $D$ be a `Descent` of $M$: a noetherian henselian local ring $D.A_0$ with an injective local map $D.\iota$ into $A$ whose image is $A \cap K_0$ for a subfield $D.K_0 \subseteq L$ with $L/K_0$ algebraic and residue field surjectivity, a proper flat model $D.X_0$ over $D.A_0$ with $M.X \cong D.X_0 \times_{D.A_0} A$, and a subfield $D.F_0 \subseteq F$ with $F/D.F_0$ algebraic and $D.F_0 \cong K(D.X_0)$ compatibly.
--
--   **Kummer exponent, divisor and its Cartier data.** Let $k \in \mathbb{N}$ have invertible image in $\kappa$ (`hk`). Let $G_i$ be divisors supported in $(C_i).\mathrm{dom}$ (`hGi`) with vanishing push-forward $\mathrm{mapDomain}\,(C_i).\mathrm{placeMap}\,(G_i) = 0$ (`hred`). Let $\iota$ be a finite type, $e : \iota \to \iota E$, $n_q : \iota \to \mathbb{Z}$, and $Q_{j,l}$ ($l \in \mathrm{Fin}\,4$) places lying in the domain of $An\,(e\,j)$ (`hQ`), subject to `hrad`, that $\mathrm{evalAt}_{Q_{j,0}}$ of the parameter equals a unit of $A$ times $\mathrm{evalAt}_{Q_{j,2}}$ of it, and `hbal`, that there is $t$ in the maximal ideal of $A$ with $\mathrm{evalAt}_{Q_{j,0}} \cdot \mathrm{evalAt}_{Q_{j,1}} = \mathrm{evalAt}_{Q_{j,2}} \cdot \mathrm{evalAt}_{Q_{j,3}} \cdot (1+t)$ on the parameter. Write $G := \sum_i G_i + \sum_j n_q(j)\bigl((Q_{j,0}) + (Q_{j,1}) - (Q_{j,2}) - (Q_{j,3})\bigr)$. Let $g \in F$, $g \ne 0$, with $\mathrm{ord}_P(g) = k\,G(P)$ for all places $P$ (`hkG`). Let $r \in \mathbb{N}$, let $U : \mathrm{Fin}\,r \to$ opens of $M.X$ with $\bigsqcup_a U_a = \top$ (`hU`), and $h : \mathrm{Fin}\,r \to F$ with all $h_a \ne 0$ (`hh`), such that: `hdiv`, $\mathrm{ord}_P(h_a) = G(P)$ whenever $M.\mathrm{pt}\,P \in U_a$; `hcoc`, for all $a,b$ and every $x \in U_a \cap U_b$ there are $t$ in the maximal ideal of $A$ and $\rho$ in the image of the stalk at $x$ inside $F$ (the subring `SemistableModel.localRing M.X M.ffEquiv x`) with $h_a = h_b(1 + t\rho)$; `hv1`, some index $a_0$ has $M.\mathrm{pt}\,P \in U_{a_0}$ exactly when $G(P) = 0$; and `hv2`, each index $a$ is of one of three shapes, namely $U_a$ meets the places exactly in $\{G = 0\}$, or there are $i$ and a place $q$ of $\bar F_i/\kappa$ such that $M.\mathrm{pt}\,P \in U_a$ iff $P$ lies in $(C_i).\mathrm{dom}$ over $q$ or else $G(P) = 0$ and $\mathrm{ord}_P(h_a) = 0$, or there is $e_0 \in \iota E$ such that $M.\mathrm{pt}\,P \in U_a$ iff $P$ lies in the domain of $An\,e_0$ or else $G(P) = 0$ and $\mathrm{ord}_P(h_a) = 0$.
--
--   **Normalising constants.** Let $c : \iota V \to L$ with all $c_i \ne 0$ (`hc0`), such that `hcunit`: whenever $M.\mathrm{gen}\,i \in U_a$, both $c_i\,(g/h_a^k)$ and its inverse lie in $(C_i).\mathrm{integers}$; and `hcslope`: $v_A(c_{\mathrm{src}(e')}) = v_A(c_{\mathrm{tgt}(e')})$ for every edge $e'$.
--
--   **The finite level.** Let $K_1$ be an intermediate field of $L/D.K_0$, finite over $D.K_0$, and put $A_1 := A \cap K_1$ (the comap of $A$ along $K_1 \to L$), assumed a noetherian henselian local ring. Let $j_1 : D.A_0 \to A_1$ and $\iota_1 : A_1 \to A$ be local ring maps with $\iota_1$ injective (`hι₁`) and $\iota_1 \circ j_1 = D.\iota$ (`hcomp`), with $\mathrm{residue}_A \circ \iota_1$ surjective (`hres₁`), with $\iota_1$ inducing on elements the inclusion $K_1 \subseteq L$ (`hι₁val`), and with $A_1$ a discrete valuation ring whenever $A \ne L$ (`hdvr`). Let $X_1$ be an integral scheme with a proper flat morphism $f_1 : X_1 \to \mathrm{Spec}\,A_1$, an isomorphism $e_1 : M.X \cong X_1 \times_{\mathrm{Spec}\,A_1} \mathrm{Spec}\,A$ with $e_1$ followed by the second projection equal to $M.\mathrm{toBase}$ (`he₁`), all stalks of $X_1$ integrally closed (`hnorm₁`), a subfield $F_1 \subseteq F$ and an isomorphism $\varphi_1 : F_1 \cong K(X_1)$, with $D.F_0 \le F_1$ (`hF₀`), the image of $K_1$ in $F$ contained in $F_1$ (`hK₁`), $F/F_1$ algebraic (`halg`), and `hcompat`, that $e_1$ followed by the first projection carries the generic point of $M.X$ to that of $X_1$ and that $\varphi_1$ is compatible with $M.\mathrm{ffEquiv}$ through the induced map on stalks at the generic point. Finally assume $g \in F_1$ (`hgF₁`), all $h_a \in F_1$ (`hhF₁`), and all $c_i \in K_1$ (`hcK₁`).
--
--   **Conclusion.** There exist $c_0 \in L$ with $c_0 \cdot g \in F_1$, an element $g_1 \in K(X_1)$, an integer $r_1$, opens $U_1 : \mathrm{Fin}\,r_1 \to$ opens of $X_1$ and $h_1 : \mathrm{Fin}\,r_1 \to K(X_1)$ such that: $c_0 \ne 0$; $g_1 = \varphi_1(c_0 \cdot g)$; $g_1 \ne 0$; the residue field of $A_1$ is algebraically closed; $k$ is a unit in $A_1$; $\bigsqcup_a U_1(a) = \top$; $h_1(a) \ne 0$ for every $a$; for every $a$ and every $x \in U_1(a)$, both $g_1/h_1(a)^k$ and $h_1(a)^k/g_1$ lie in the image of the stalk $\mathcal{O}_{X_1,x}$ in $K(X_1)$; for all $a, b$ and every $x \in U_1(a) \cap U_1(b)$ there are $t$ in the maximal ideal of $A_1$ and $s$ in the image of $\mathcal{O}_{X_1,x}$ in $K(X_1)$ with $h_1(a) = h_1(b)\bigl(1 + \mathrm{baseToFunctionField}\,f_1(t)\cdot s\bigr)$, where $\mathrm{baseToFunctionField}\,f_1$ is the ring map $A_1 \to K(X_1)$ obtained from $f_1$ on global sections followed by the germ at the generic point; and the map on global sections induced by the projection $X_1 \times_{\mathrm{Spec}\,A_1} \mathrm{Spec}\,\kappa(A_1) \to \mathrm{Spec}\,\kappa(A_1)$ is bijective.
--
--   This is the level-transfer step of the kernel-of-reduction argument: the Kummer–Cartier data $(g, (U_a,h_a), c_i)$ attached to a semistable model over the (possibly non-noetherian) valuation ring $A$ are rewritten, after rescaling $g$ by a constant, as data on the model $X_1$ over the noetherian henselian base $A_1 = A \cap K_1$, together with the algebraic closedness of $\kappa(A_1)$, the invertibility of $k$ there, and the fact that the closed fibre of $f_1$ has $\kappa(A_1)$ as its ring of global sections. It is used by [`AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent`](thm.html#AlgebraicCurve.mem_principal_of_zsmul_mem_principal_of_forall_mapDomain_placeMap_eq_zero_of_genusFF_of_semistableModel_of_descent), where the descended data are the input to the construction of a Kummer covering over the level base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_SemistableModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

universe u

theorem AlgebraicCurve.exists_cartierData_kummer_finiteLevel_of_cartierData_of_balanced_of_semistableModel_of_descent
    {L : Type u} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (π : A) (hπ : π ∈ IsLocalRing.maximalIdeal A) (hπ0 : π ≠ 0)
    (hrk : ∀ x : L, x ≠ 0 → ∀ y : A, y ∈ IsLocalRing.maximalIdeal A →
      ∃ n : ℕ, A.valuation ((y : L) ^ n) ≤ A.valuation x)
    (F : Type*) [Field F] [Algebra L F]
    {ιV ιE : Type*} [Fintype ιV] [Fintype ιE] (Fbar : ιV → Type*) [∀ i, Field (Fbar i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fbar i)]
    (hratBar : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q.IsRational)
    (C : ∀ i, ComponentChart A F (Fbar i))
    (hratF : ∀ i, ∀ P ∈ (C i).dom, P.IsRational)
    (An An' : ιE → Annulus A F) (src tgt : ιE → ιV)
    (xs : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (src e)))
    (xt : ∀ e, Place (IsLocalRing.ResidueField A) (Fbar (tgt e)))
    (w : ιE → ℕ)
    (hpair : ∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
      ((An e).modulus : L) ≠ 0 ∧
      (An' e).param * (An e).param = algebraMap L F ((An e).modulus : L))
    (hw : ∀ e, ∃ u : Aˣ, (An e).modulus = u * π ^ w e)
    (hatt : ∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e))
    (hnodes : (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : ιE ⊕ ιE,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField A) (Fbar j)))
          (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E'))
    (hcover : ∀ P : Place L F,
      (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
      (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom))
    (hdisc : ∀ i, ∀ Q : Place (IsLocalRing.ResidueField A) (Fbar i), Q ∉ (C i).nodes →
      ∃ (T : F) (hT : T ∈ (C i).integers), (C i).residue ⟨T, hT⟩ ≠ 0 ∧ Q.ord ((C i).residue ⟨T, hT⟩) = 1 ∧
        (∀ P ∈ (C i).dom, (C i).placeMap P = Q → T ∈ P.toValuationSubring ∧
          ∃ h : P.evalAt T ∈ A, (⟨P.evalAt T, h⟩ : A) ∈ IsLocalRing.maximalIdeal A) ∧
        ∀ c : A, c ∈ IsLocalRing.maximalIdeal A →
          ∃! P : Place L F, P ∈ (C i).dom ∧ (C i).placeMap P = Q ∧ P.evalAt T = c)
    (hgenus : genusFF L F + Fintype.card ιV =
      (∑ i, genusFF (IsLocalRing.ResidueField A) (Fbar i)) + Fintype.card ιE + 1)
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    [∀ i, IsCurveOver (IsLocalRing.ResidueField A) (Fbar i)]
    [∀ i, Algebra.EssFiniteType (IsLocalRing.ResidueField A) (Fbar i)]
    (M : SemistableModel A F Fbar C An src tgt xs xt) (D : M.Descent)
    (k : ℕ) (hk : IsUnit ((k : ℕ) : IsLocalRing.ResidueField A))
    (Gi : ιV → Divisor L F) (hGi : ∀ i, ∀ P ∈ (Gi i).support, P ∈ (C i).dom)
    (hred : ∀ i, Finsupp.mapDomain (C i).placeMap (Gi i) = 0)
    {ι : Type*} [Fintype ι] (e : ι → ιE) (nq : ι → ℤ) (Q : ι → Fin 4 → Place L F)
    (hQ : ∀ j l, Q j l ∈ (An (e j)).dom)
    (hrad : ∀ j, ∃ u : Aˣ,
      (Q j 0).evalAt (An (e j)).param = ((u : A) : L) * (Q j 2).evalAt (An (e j)).param)
    (hbal : ∀ j, ∃ t ∈ IsLocalRing.maximalIdeal A,
      (Q j 0).evalAt (An (e j)).param * (Q j 1).evalAt (An (e j)).param =
        (Q j 2).evalAt (An (e j)).param * (Q j 3).evalAt (An (e j)).param * (1 + ((t : A) : L)))
    (g : F) (hg : g ≠ 0)
    (hkG : ∀ P : Place L F, P.ord g = (k : ℤ) *
      (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P)

    (r : ℕ) (U : Fin r → M.X.Opens) (h : Fin r → F)
    (hU : (⨆ a, U a) = ⊤) (hh : ∀ a, h a ≠ 0)
    (hdiv : ∀ a (P : Place L F), M.pt P ∈ U a → P.ord (h a) =
        (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P)
    (hcoc : ∀ a b (x : M.X), x ∈ U a → x ∈ U b →
        ∃ t ∈ IsLocalRing.maximalIdeal A, ∃ r ∈ SemistableModel.localRing M.X M.ffEquiv x,
          h a = h b * (1 + algebraMap L F ((t : A) : L) * r))
    (hv1 : ∃ a₀, ∀ P : Place L F, M.pt P ∈ U a₀ ↔
        (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P = 0)
    (hv2 : ∀ a, (∀ P : Place L F, M.pt P ∈ U a ↔
          (∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P = 0) ∨
        (∃ (i : ιV) (q : Place (IsLocalRing.ResidueField A) (Fbar i)), ∀ P : Place L F,
          M.pt P ∈ U a ↔ ((P ∈ (C i).dom ∧ (C i).placeMap P = q) ∨
            ((∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P = 0 ∧ P.ord (h a) = 0))) ∨
        (∃ e₀ : ιE, ∀ P : Place L F,
          M.pt P ∈ U a ↔ (P ∈ (An e₀).dom ∨
            ((∑ i, Gi i + ∑ j, nq j • (Finsupp.single (Q j 0) 1 + Finsupp.single (Q j 1) 1
          - Finsupp.single (Q j 2) 1 - Finsupp.single (Q j 3) 1)) P = 0 ∧ P.ord (h a) = 0))))

    (c : ιV → L) (hc0 : ∀ i, c i ≠ 0)
    (hcunit : ∀ i a, M.gen i ∈ U a →
        c i • (g / h a ^ k) ∈ (C i).integers ∧ (c i • (g / h a ^ k))⁻¹ ∈ (C i).integers)
    (hcslope : ∀ e', A.valuation (c (src e')) = A.valuation (c (tgt e')))

    (K₁ : IntermediateField ↥D.K₀ L) [FiniteDimensional ↥D.K₀ ↥K₁]
    [IsNoetherianRing ↥(A.comap (algebraMap ↥K₁ L))] [HenselianLocalRing ↥(A.comap (algebraMap ↥K₁ L))]
    (j₁ : D.A₀ →+* ↥(A.comap (algebraMap ↥K₁ L))) (ι₁ : ↥(A.comap (algebraMap ↥K₁ L)) →+* A) [IsLocalHom j₁] [IsLocalHom ι₁]
    (hι₁ : Function.Injective ι₁) (hcomp : ι₁.comp j₁ = D.ι)
    (hres₁ : Function.Surjective ((IsLocalRing.residue A).comp ι₁))
    (hι₁val : ∀ x : ↥(A.comap (algebraMap ↥K₁ L)), ((ι₁ x : A) : L) = algebraMap ↥K₁ L (x : ↥K₁))
    (hdvr : A ≠ ⊤ → IsDiscreteValuationRing ↥(A.comap (algebraMap ↥K₁ L)))

    (X₁ : Scheme.{u}) [IsIntegral X₁] (f₁ : X₁ ⟶ Spec (CommRingCat.of ↥(A.comap (algebraMap ↥K₁ L)))) [IsProper f₁] [Flat f₁]
    (e₁ : M.X ≅ pullback f₁ (Spec.map (CommRingCat.ofHom ι₁)))
    (he₁ : e₁.hom ≫ pullback.snd f₁ (Spec.map (CommRingCat.ofHom ι₁)) = M.toBase)
    (hnorm₁ : ∀ x : X₁, IsIntegrallyClosed (X₁.presheaf.stalk x))
    (F₁ : Subfield F) (φ₁ : F₁ ≃+* X₁.functionField)
    (hF₀ : D.F₀ ≤ F₁) (hK₁ : ∀ x : L, x ∈ K₁ → algebraMap L F x ∈ F₁) (halg : Algebra.IsAlgebraic F₁ F)
    (hcompat : ∃ hgen : (e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).base (genericPoint M.X) =
        genericPoint X₁,
      ∀ s : F₁, M.ffEquiv (s : F) =
        ((e₁.hom ≫ pullback.fst f₁ (Spec.map (CommRingCat.ofHom ι₁))).stalkMap (genericPoint M.X)).hom
          ((X₁.presheaf.stalkSpecializes (specializes_of_eq hgen)).hom (φ₁ s)))

    (hgF₁ : g ∈ F₁) (hhF₁ : ∀ a, h a ∈ F₁) (hcK₁ : ∀ i, c i ∈ K₁) :
    ∃ (c₀ : L) (hc₀F₁ : c₀ • g ∈ F₁) (g₁ : X₁.functionField)
      (r₁ : ℕ) (U₁ : Fin r₁ → X₁.Opens) (h₁ : Fin r₁ → X₁.functionField),
      c₀ ≠ 0 ∧ g₁ = φ₁ ⟨c₀ • g, hc₀F₁⟩ ∧ g₁ ≠ 0 ∧
      IsAlgClosed (IsLocalRing.ResidueField ↥(A.comap (algebraMap ↥K₁ L))) ∧ IsUnit ((k : ℕ) : ↥(A.comap (algebraMap ↥K₁ L))) ∧
      (⨆ a, U₁ a) = ⊤ ∧ (∀ a, h₁ a ≠ 0) ∧
      (∀ a (x : X₁), x ∈ U₁ a →
        g₁ / h₁ a ^ k ∈ (algebraMap (X₁.presheaf.stalk x) X₁.functionField).range ∧
        h₁ a ^ k / g₁ ∈ (algebraMap (X₁.presheaf.stalk x) X₁.functionField).range) ∧
      (∀ a b (x : X₁), x ∈ U₁ a → x ∈ U₁ b →
        ∃ t ∈ IsLocalRing.maximalIdeal ↥(A.comap (algebraMap ↥K₁ L)), ∃ s ∈ (algebraMap (X₁.presheaf.stalk x) X₁.functionField).range,
          h₁ a = h₁ b * (1 + AlgebraicCurve.SemistableModel.baseToFunctionField f₁ t * s)) ∧
      Function.Bijective
        (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥(A.comap (algebraMap ↥K₁ L)))))).appTop := by sorry
